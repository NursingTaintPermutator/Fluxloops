package com.example.fluxloops


import android.app.KeyguardManager
import android.content.BroadcastReceiver
import android.content.Context
import android.content.Intent
import android.content.IntentFilter
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.LinearGradient
import android.graphics.Paint
import android.graphics.Shader
import android.os.Build
import android.os.Bundle
import android.os.PowerManager
import android.service.wallpaper.WallpaperService
import android.util.Log
import android.view.Choreographer
import android.view.GestureDetector
import android.view.MotionEvent
import android.view.SurfaceHolder
import android.view.animation.Interpolator
import android.view.animation.PathInterpolator
import kotlin.math.abs
import kotlin.math.cos
import kotlin.math.exp
import kotlin.math.hypot
import kotlin.math.max
import kotlin.math.min
import kotlin.math.sin

// Zustandsvektor eines Rings: Position, Tiefe, Größe, Kippwinkel, Deckkraft, 8 Formwerte
private const val X = 0
private const val Y = 1
private const val H = 2
private const val S = 3
private const val RX = 4
private const val RY = 5
private const val A = 6
private const val SH = 7
private const val N = 15

private const val PER = 40            // Stützpunkte pro Viertelbogen (viele = runde Kurve ohne Knicke)
private const val TOTAL = 4 * PER
private const val SEC = 1_000_000_000L
private const val KAPPA = 0.55228f

class LoopsWallpaperService : WallpaperService() {

    override fun onCreateEngine(): Engine = LoopsEngine()

    /** Ein Ring (Loop) im 3D-Raum. Bis zu 6 gleichzeitig, neue Ringe verdrängen die ältesten. */
    private class Ring(
        val uWidth: Float,   // Breite des Bandes (Anteil)
        val jScale: Float,   // Startgröße, begrenzt die Breite bei größeren Ringen
        val colorA: Int,
        val colorB: Int
    ) {
        val cur = FloatArray(N)
        val from = FloatArray(N)
        val to = FloatArray(N)
        var depth = 0f       // 0 = vorne (scharf), größer = näher an der Kamera (unschärfer)
        var startNs = 0L
        var delayNs = 0L
        var durNs = 1L
        var interp = 0
        var fading = false

        fun active(now: Long): Boolean = now < startNs + delayNs + durNs
    }

    inner class LoopsEngine : Engine(), Choreographer.FrameCallback {

        private val tag = "LoopsWP"

        // ---- Einstellungen zum Anpassen ------------------------------------------
        private val lineWidthScale = 1.4f   // Liniendicke insgesamt
        private val glowStrength = 1.0f     // Stärke des Scheins an hellen Stellen (0 = aus)

        // Rottöne wie bisher
        private val light = Color.parseColor("#D6A2A7")
        private val mid = Color.parseColor("#CD7588")
        private val dark = Color.parseColor("#B55D63")
        private val palette = intArrayOf(light, mid, dark)

        // ---- Zustand --------------------------------------------------------------
        private val rnd = java.util.Random()
        private val rings = arrayOfNulls<Ring>(6)
        private var nextSlot = 0

        private var screenW = 1
        private var screenH = 1
        private var visible = false
        private var scheduled = false
        private var launched = false
        private var pending = 0           // 1 = Bildschirm an (gesperrt), 2 = entsperrt
        private var camC0 = 0f            // Seitenposition des Startbildschirms minus 0,5
        private var pane = 0f             // Seite -1..1, Zielposition der Ringe hängt davon ab
        private var gotSwitchPage = false
        private var widthBase = 0.05f
        private var lastCmdMs = 0L

        private val interps: Array<Interpolator> = arrayOf(
            PathInterpolator(0.0f, 0.0f, 0.2f, 1.0f),
            PathInterpolator(0.075f, 0.0f, 0.2f, 1.0f),
            PathInterpolator(0.2f, 0.0f, 0.3f, 1.0f),
            PathInterpolator(0.7f, 0.0f, 0.3f, 1.0f)
        )
        private val touchRise: Interpolator = PathInterpolator(0.2f, 0.0f, 0.3f, 1.0f)
        private val touchFall: Interpolator = PathInterpolator(0.0f, 0.0f, 0.2f, 1.0f)

        // Berührung: Linien werden zum Finger gezogen
        private var tpDown = false
        private var tpDownMs = 0L
        private var tpX0 = 0f
        private var tpY0 = 0f
        private var tpX = 0f
        private var tpY = 0f
        private var tpRelStr = 0f
        private var tpRelMs = 0L

        // Zeichenpuffer
        private val cp = FloatArray(24)
        private val sxA = FloatArray(TOTAL)
        private val syA = FloatArray(TOTAL)
        private val ndxA = FloatArray(TOTAL)
        private val ndyA = FloatArray(TOTAL)
        private val zcA = FloatArray(TOTAL)
        private val sclA = FloatArray(TOTAL)
        private val ptA = FloatArray(TOTAL)

        private val bgPaint = Paint()
        private val linePaint = Paint(Paint.ANTI_ALIAS_FLAG).apply {
            style = Paint.Style.STROKE
            strokeCap = Paint.Cap.BUTT
        }

        private val gestures = GestureDetector(
            this@LoopsWallpaperService,
            object : GestureDetector.SimpleOnGestureListener() {
                override fun onFling(
                    e1: MotionEvent?, e2: MotionEvent, velocityX: Float, velocityY: Float
                ): Boolean {
                    if (e1 == null) return false
                    val dx = velocityX / 32f + (e2.x - e1.x)
                    val dy = velocityY / 32f + (e2.y - e1.y)
                    fling(dx * 0.5625f / screenW, dy * 0.75f / screenH)
                    return true
                }
            }
        )

        private val screenReceiver = object : BroadcastReceiver() {
            override fun onReceive(context: Context, intent: Intent) {
                val pm = this@LoopsWallpaperService.getSystemService(Context.POWER_SERVICE) as PowerManager
                val km = this@LoopsWallpaperService.getSystemService(Context.KEYGUARD_SERVICE) as KeyguardManager
                Log.d(tag, "Broadcast " + intent.action)
                when (intent.action) {
                    Intent.ACTION_SCREEN_OFF -> if (!pm.isInteractive) eventScreenOff()
                    Intent.ACTION_SCREEN_ON -> post(if (km.isKeyguardLocked) 1 else 2)
                    Intent.ACTION_USER_PRESENT -> post(2)
                }
            }
        }

        // ---- Lebenszyklus ---------------------------------------------------------

        override fun onCreate(surfaceHolder: SurfaceHolder) {
            super.onCreate(surfaceHolder)
            setTouchEventsEnabled(true)
            val filter = IntentFilter().apply {
                addAction(Intent.ACTION_SCREEN_ON)
                addAction(Intent.ACTION_SCREEN_OFF)
                addAction(Intent.ACTION_USER_PRESENT)
            }
            if (Build.VERSION.SDK_INT >= 33) {
                this@LoopsWallpaperService.registerReceiver(
                    screenReceiver, filter, Context.RECEIVER_NOT_EXPORTED
                )
            } else {
                this@LoopsWallpaperService.registerReceiver(screenReceiver, filter)
            }
        }

        override fun onDestroy() {
            super.onDestroy()
            Choreographer.getInstance().removeFrameCallback(this)
            try {
                this@LoopsWallpaperService.unregisterReceiver(screenReceiver)
            } catch (e: IllegalArgumentException) {
                // war nicht registriert
            }
        }

        override fun onSurfaceChanged(holder: SurfaceHolder, format: Int, width: Int, height: Int) {
            super.onSurfaceChanged(holder, format, width, height)
            screenW = max(1, width)
            screenH = max(1, height)
            val shortSide = min(screenW, screenH).toFloat()
            val r = (1080f / shortSide) * (1080f / shortSide) * 0.05f
            widthBase = max(0.05f, r)
            bgPaint.shader = LinearGradient(
                0f, 0f, 0f, screenH.toFloat(),
                Color.parseColor("#1C0000"), Color.parseColor("#050000"),
                Shader.TileMode.CLAMP
            )
            requestFrame()
        }

        override fun onVisibilityChanged(visible: Boolean) {
            this.visible = visible
            if (visible) {
                if (!launched) {
                    launched = true
                    launch()
                }
                if (pending != 0) {
                    val kind = pending
                    pending = 0
                    fire(kind)
                }
                requestFrame()
            } else {
                Choreographer.getInstance().removeFrameCallback(this)
                scheduled = false
            }
        }

        override fun onSurfaceDestroyed(holder: SurfaceHolder) {
            super.onSurfaceDestroyed(holder)
            visible = false
            Choreographer.getInstance().removeFrameCallback(this)
            scheduled = false
        }

        // Startbildschirm wird verschoben: Kamera fährt seitlich (Parallaxe durch die Tiefe der Ringe)
        override fun onOffsetsChanged(
            xOffset: Float, yOffset: Float,
            xOffsetStep: Float, yOffsetStep: Float,
            xPixelOffset: Int, yPixelOffset: Int
        ) {
            camC0 = xOffset - 0.5f
            if (!gotSwitchPage) pane = camC0 * 2f
            requestFrame()
        }

        // ---- Befehle vom Launcher und von der Sperrbildschirm-App ----------------

        override fun onCommand(
            action: String?, x: Int, y: Int, z: Int,
            extras: Bundle?, resultRequested: Boolean
        ): Bundle? {
            val now = System.currentTimeMillis()
            if (action != null) {
                Log.d(tag, "Command $action")
                when (action) {
                    "com.sonymobile.home.wallpaper.command.SWITCH_PAGE" -> if (extras != null) {
                        val to = extras.getInt("switch_to_page").toFloat()
                        val count = max(1, extras.getInt("page_count")).toFloat()
                        pane = (((to + 1f) / count) - 0.5f) * 2f
                        gotSwitchPage = true
                    }
                    "android.wallpaper.tap" -> if (now - lastCmdMs > 60) {
                        addCircle(
                            ((x.toFloat() / screenW) * 2f - 1f) * 1.3f,
                            -(((y.toFloat() / screenH) * 2f - 1f) * (screenH * 1.3f / screenW))
                        )
                        requestFrame()
                    }
                    "com.sonymobile.lockscreen.wallpaper.command.FPA_ACQUIRED",
                    "com.sonymobile.lockscreen.wallpaper.command.FPA_ERROR" -> if (now - lastCmdMs > 60) {
                        if (extras != null && extras.getInt("reason") == 6) {
                            fingerprint(0.2f, SEC)      // Finger liegt auf dem Sensor
                        } else {
                            fingerprint(0.9f, SEC / 2)  // Fehler
                        }
                    }
                }
                lastCmdMs = now
            }
            return super.onCommand(action, x, y, z, extras, resultRequested)
        }

        override fun onTouchEvent(event: MotionEvent) {
            gestures.onTouchEvent(event)
            when (event.actionMasked) {
                MotionEvent.ACTION_DOWN -> {
                    tpDown = true
                    tpDownMs = System.currentTimeMillis()
                    tpX0 = event.x
                    tpY0 = event.y
                    tpX = event.x
                    tpY = event.y
                    requestFrame()
                }
                MotionEvent.ACTION_MOVE -> {
                    tpX = event.x
                    tpY = event.y
                    requestFrame()
                }
                MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {
                    if (tpDown) {
                        tpRelStr = touchStrength(System.currentTimeMillis())
                        tpRelMs = System.currentTimeMillis()
                        tpDown = false
                        requestFrame()
                    }
                }
            }
        }

        // ---- Ereignisse (Zielwerte entsprechen dem Original) ----------------------

        private fun post(kind: Int) {
            if (visible) fire(kind) else pending = max(pending, kind)
        }

        private fun fire(kind: Int) {
            if (kind == 1) eventScreenOn() else eventUserPresent()
        }

        private fun launch() {
            for (i in 0 until 5) addCircle(0f, 0f)
        }

        // Bildschirm aus: alle Ringe schrumpfen am rechten Rand auf null
        private fun eventScreenOff() {
            pending = 0
            moveAll8(2.0f + 0.8f * pane, 0.3f, 0f, 0f, 0f, SEC / 10, 0)
        }

        // Bildschirm an (gesperrt): Ringe wachsen am rechten Rand und laufen leicht nach links
        private fun eventScreenOn() {
            moveAll9(
                2.0f + 0.8f * pane, 0.3f, 1.5f + 0.8f * pane, 0.3f,
                1.2f, 1.3f, 0.1f, SEC, 0
            )
            requestFrame()
        }

        // Entsperrt: Ringe wachsen auf volle Größe und sammeln sich am rechten Rand
        private fun eventUserPresent() {
            moveAll8(1.5f + 0.8f * pane, 0.3f, 1.5f, 1.8f, 0.1f, 2 * SEC, 0)
            requestFrame()
        }

        // Finger auf dem Fingerabdrucksensor
        private fun fingerprint(jitter: Float, durNs: Long) {
            moveAll8(0.8f * pane + 1.5f, 0.3f, 1.2f, 1.3f, jitter, durNs, 0)
            requestFrame()
        }

        // Wischgeste: Ringe wandern, die vorderen am stärksten (Tiefe bestimmt den Weg)
        private fun fling(fx: Float, fy: Float) {
            val now = System.nanoTime()
            val lo = -2f + camC0 * 2f
            val hi = 2f + camC0 * 2f
            for (r in rings) {
                if (r == null || r.fading) continue
                evaluate(r, now)
                System.arraycopy(r.cur, 0, r.from, 0, N)
                System.arraycopy(r.cur, 0, r.to, 0, N)
                val k = 1.5f - r.depth
                r.to[X] = max(lo, min(hi, r.cur[X] + k * fx))
                r.to[Y] = max(-1.7f, min(1.7f, r.cur[Y] - k * fy))
                r.to[H] = r.depth
                val delay = (rnd.nextFloat() * 0.1f * SEC).toLong()
                begin(r, now, SEC - delay, 1, delay)
            }
            requestFrame()
        }

        // ---- Ringe verwalten ------------------------------------------------------

        private fun rand(a: Float, b: Float): Float = a + rnd.nextFloat() * (b - a)

        private fun jitter(f: Float): Float {
            val v = rnd.nextFloat() * f - f / 2f
            return if (v >= f / 6f || v <= -f / 6f) v else 0f
        }

        private fun evaluate(r: Ring, now: Long) {
            val t = (now - r.startNs - r.delayNs).toFloat() / r.durNs.toFloat()
            val e = if (t <= 0f) 0f else if (t >= 1f) 1f else interps[r.interp].getInterpolation(t)
            for (i in 0 until N) r.cur[i] = r.from[i] + (r.to[i] - r.from[i]) * e
        }

        private fun begin(r: Ring, now: Long, durNs: Long, interp: Int, delayNs: Long) {
            r.startNs = now
            r.durNs = max(1L, durNs)
            r.delayNs = delayNs
            r.interp = interp
        }

        // Ring bewegt sich zu einer neuen Position/Größe, Kippung und Form ändern sich zufällig
        private fun moveRing(
            r: Ring, now: Long, x: Float, y: Float, scale: Float,
            jitterAmount: Float, durNs: Long, interp: Int
        ) {
            if (r.fading) return
            evaluate(r, now)
            System.arraycopy(r.cur, 0, r.from, 0, N)
            r.to[X] = x
            r.to[Y] = y
            r.to[H] = r.depth
            r.to[S] = scale
            r.to[RX] = 0.3927f * (rnd.nextFloat() * 2f - 1f)
            r.to[RY] = 0.3927f * (rnd.nextFloat() * 2f - 1f)
            for (k in 0 until 8) r.to[SH + k] = jitter(jitterAmount)
            begin(r, now, durNs, interp, 0L)
        }

        private fun moveAll8(
            x: Float, y: Float, sMin: Float, sMax: Float,
            jitterAmount: Float, durNs: Long, interp: Int
        ) {
            val now = System.nanoTime()
            for (r in rings) {
                if (r == null) continue
                val d = (rand(0.7f, 1f) * durNs).toLong()
                moveRing(r, now, x, y, rand(sMin, sMax), jitterAmount, d, interp)
            }
        }

        // Wie moveAll8, aber Ringe starten zuerst unsichtbar (Größe 0) am Ausgangspunkt
        private fun moveAll9(
            fromX: Float, fromY: Float, toX: Float, toY: Float, sMin: Float, sMax: Float,
            jitterAmount: Float, durNs: Long, interp: Int
        ) {
            val now = System.nanoTime()
            for (r in rings) {
                if (r == null || r.fading) continue
                evaluate(r, now)
                System.arraycopy(r.cur, 0, r.to, 0, N)
                r.cur[X] = fromX
                r.cur[Y] = fromY
                r.cur[H] = r.depth
                r.cur[S] = 0f
                System.arraycopy(r.cur, 0, r.from, 0, N)
                System.arraycopy(r.cur, 0, r.to, 0, N)
                r.startNs = 0L
                r.delayNs = 0L
                r.durNs = 1L
                val d = (rand(0.7f, 1f) * durNs).toLong()
                moveRing(r, now, toX, toY, rand(sMin, sMax), jitterAmount, d, interp)
            }
        }

        // Neuer Ring (Start oder Tippen): wächst an der Stelle, ältere werden unschärfer
        private fun addCircle(sx: Float, sy: Float) {
            val now = System.nanoTime()
            val x = sx + camC0
            val scaleTarget = rand(1.5f, 1.6f)
            val ring = Ring(
                rand(widthBase, 0.16f), scaleTarget,
                palette[rnd.nextInt(3)], palette[rnd.nextInt(3)]
            )
            ring.cur[X] = x
            ring.cur[Y] = sy
            ring.cur[H] = 0f
            ring.cur[S] = 0.4f * scaleTarget
            ring.cur[A] = 0f
            System.arraycopy(ring.cur, 0, ring.from, 0, N)
            System.arraycopy(ring.cur, 0, ring.to, 0, N)
            ring.to[S] = scaleTarget
            ring.to[A] = 0.98f
            ring.to[RX] = 0.3927f * (rnd.nextFloat() * 2f - 1f)
            ring.to[RY] = 0.3927f * (rnd.nextFloat() * 2f - 1f)
            for (k in 0 until 8) ring.to[SH + k] = jitter(0.1f)
            ring.cur[RX] = 0.3927f * (rnd.nextFloat() * 2f - 1f)
            ring.cur[RY] = 0.3927f * (rnd.nextFloat() * 2f - 1f)
            System.arraycopy(ring.cur, 0, ring.from, 0, N)
            begin(ring, now, SEC, 0, 0L)

            // Ältere Ringe rücken eine Tiefenstufe nach hinten (näher zur Kamera = unschärfer)
            for (o in rings) {
                if (o == null) continue
                o.depth += 0.3f
                if (!o.fading) {
                    val tx = o.to[X]
                    val ty = o.to[Y]
                    val ts = o.to[S]
                    moveRing(o, now, tx, ty, ts, 0.3f, SEC, 0)
                }
            }

            rings[nextSlot] = ring
            nextSlot = if (nextSlot == 5) 0 else nextSlot + 1

            // Der nächste Platz ist der älteste Ring: er blendet aus
            val oldest = rings[nextSlot]
            if (oldest != null && !oldest.fading) {
                evaluate(oldest, now)
                System.arraycopy(oldest.cur, 0, oldest.from, 0, N)
                System.arraycopy(oldest.cur, 0, oldest.to, 0, N)
                oldest.to[H] = oldest.depth + 0.3f
                oldest.to[A] = 0f
                oldest.fading = true
                begin(oldest, now, SEC, 0, 0L)
            }
        }

        // ---- Berührung ------------------------------------------------------------

        private fun touchStrength(nowMs: Long): Float {
            if (tpDown) {
                val dist = hypot((tpX - tpX0) / (screenW / 2f), (tpY - tpY0) / (screenH / 2f))
                val t = ((nowMs - tpDownMs) - 150f / (dist + 1f)) / 300f
                return if (t <= 0f) 0f else touchRise.getInterpolation(min(1f, t))
            }
            if (tpRelStr > 0f) {
                val p = touchFall.getInterpolation(min(1f, (nowMs - tpRelMs) / 900f))
                return max(0f, tpRelStr - p)
            }
            return 0f
        }

        // ---- Animation ------------------------------------------------------------

        private fun requestFrame() {
            if (!visible || scheduled) return
            scheduled = true
            Choreographer.getInstance().postFrameCallback(this)
        }

        override fun doFrame(frameTimeNanos: Long) {
            scheduled = false
            if (!visible) return
            val now = System.nanoTime()
            drawFrame(now)

            var animating = tpDown
            if (!animating) {
                for (r in rings) {
                    if (r != null && r.active(now)) {
                        animating = true
                        break
                    }
                }
            }
            if (!animating && touchStrength(System.currentTimeMillis()) > 0f) animating = true
            if (animating) requestFrame()
        }

        // ---- Zeichnen -------------------------------------------------------------

        private fun smooth(a: Float, b: Float, x: Float): Float {
            val t = min(1f, max(0f, (x - a) / (b - a)))
            return t * t * (3f - 2f * t)
        }

        private fun drawFrame(now: Long) {
            if (screenW <= 1) return
            val holder = surfaceHolder
            val canvas = try {
                holder.lockHardwareCanvas()
            } catch (e: Exception) {
                try {
                    holder.lockCanvas()
                } catch (e2: Exception) {
                    null
                }
            } ?: return

            try {
                canvas.drawRect(0f, 0f, screenW.toFloat(), screenH.toFloat(), bgPaint)
                val ts = touchStrength(System.currentTimeMillis())
                for (r in rings) {
                    if (r == null) continue
                    evaluate(r, now)
                    drawRing(canvas, r, ts)
                }
            } finally {
                holder.unlockCanvasAndPost(canvas)
            }
        }

        private fun setCp(i: Int, x: Float, y: Float) {
            cp[2 * i] = x
            cp[2 * i + 1] = y
        }

        // Kreis aus vier Bézier-Stücken, die 8 Formwerte verbiegen die Griffpunkte
        private fun buildControl(c: FloatArray) {
            val a1 = c[SH]
            val a2 = c[SH + 1]
            val a3 = c[SH + 2]
            val a4 = c[SH + 3]
            val a5 = c[SH + 4]
            val a6 = c[SH + 5]
            val a7 = c[SH + 6]
            val a8 = c[SH + 7]
            setCp(0, 1f, 0f)
            setCp(1, 1f - a7, KAPPA - a8)
            setCp(2, KAPPA + a1, 1f + a2)
            setCp(3, 0f, 1f)
            setCp(4, -KAPPA - a1, 1f - a2)
            setCp(5, a3 - 1f, KAPPA + a4)
            setCp(6, -1f, 0f)
            setCp(7, -1f - a3, -KAPPA - a4)
            setCp(8, a5 - KAPPA, a6 - 1f)
            setCp(9, 0f, -1f)
            setCp(10, KAPPA - a5, -1f - a6)
            setCp(11, 1f + a7, a8 - KAPPA)
        }

        private fun drawRing(canvas: Canvas, r: Ring, touchS: Float) {
            val c = r.cur
            val alphaState = c[A]
            val scale = c[S]
            if (alphaState < 0.01f || scale < 0.03f) return

            buildControl(c)
            val cosRx = cos(c[RX])
            val sinRx = sin(c[RX])
            val cosRy = cos(c[RY])
            val sinRy = sin(c[RY])
            val aspect = screenH.toFloat() / screenW
            val camX = 1.5f * camC0

            // Punkte des Rings in den 3D-Raum, dann perspektivisch auf den Bildschirm
            for (patch in 0 until 4) {
                val i0 = 3 * patch
                val i1 = (i0 + 1) % 12
                val i2 = (i0 + 2) % 12
                val i3 = (i0 + 3) % 12
                for (s in 0 until PER) {
                    val t = s.toFloat() / PER
                    val u = 1f - t
                    val b0 = u * u * u
                    val b1 = 3f * t * u * u
                    val b2 = 3f * t * t * u
                    val b3 = t * t * t
                    val px = b0 * cp[2 * i0] + b1 * cp[2 * i1] + b2 * cp[2 * i2] + b3 * cp[2 * i3]
                    val py = b0 * cp[2 * i0 + 1] + b1 * cp[2 * i1 + 1] + b2 * cp[2 * i2 + 1] + b3 * cp[2 * i3 + 1]

                    val x1 = px * scale
                    val y1 = py * scale
                    val yr = y1 * cosRx
                    val zr = y1 * sinRx
                    val xr = x1 * cosRy + zr * sinRy
                    val zr2 = -x1 * sinRy + zr * cosRy

                    val xv = c[X] + xr - camX
                    val yv = c[Y] + yr
                    val dist = max(10.5f, 13f - c[H] + zr2)
                    val sc = 10f / dist
                    val ndx = xv * sc
                    val ndy = yv * sc / aspect
                    var sx = (ndx * 0.5f + 0.5f) * screenW
                    var sy = (0.5f - ndy * 0.5f) * screenH

                    if (touchS > 0f) {
                        // Sanfte, großräumige Verschiebung zum Finger: alle Ringe wandern ein Stück
                        // mit und verbiegen sich nur leicht, ohne lokale Beulen am Finger
                        val dx = tpX - sx
                        val dy = tpY - sy
                        val soft = hypot(dx, dy) + 0.5f * screenW
                        val wide = hypot(dx, dy) / (1.6f * screenW)
                        val pull = touchS * 0.2f * screenW * exp(-wide * wide)
                        sx += dx / soft * pull
                        sy += dy / soft * pull
                    }

                    val idx = patch * PER + s
                    sxA[idx] = sx
                    syA[idx] = sy
                    ndxA[idx] = ndx
                    ndyA[idx] = ndy
                    zcA[idx] = 1.6667f * dist - 26.667f
                    sclA[idx] = sc
                    ptA[idx] = t
                }
            }

            val uwEff = r.uWidth * min(r.jScale / max(scale, 0.01f), 1f)
            val ar = Color.red(r.colorA).toFloat()
            val ag = Color.green(r.colorA).toFloat()
            val ab = Color.blue(r.colorA).toFloat()
            val br0 = Color.red(r.colorB).toFloat()
            val bg0 = Color.green(r.colorB).toFloat()
            val bb0 = Color.blue(r.colorB).toFloat()

            for (i in 0 until TOTAL) {
                val j = (i + 1) % TOTAL
                // Tiefenschärfe: außerhalb der Schärfeebene wird das Band blasser
                val zc = (zcA[i] + zcA[j]) * 0.5f
                val d1 = max((zc + 4f) * (zc + 4f) * 0.5f, 1f)
                val d2 = max((zc + 5f) * (zc + 5f) * 0.5f, 1f)
                val alpha = min(1f, uwEff * 20f / d1) / d2 * 0.98f * alphaState
                if (alpha < 0.012f) continue

                // Beleuchtung: oben links hell, unten rechts dunkel
                val nx = (ndxA[i] + ndxA[j]) * 0.5f
                val ny = (ndyA[i] + ndyA[j]) * 0.5f
                val lit = smooth(-0.35f, 0.55f, -0.65f * ny - 0.35f * nx)

                val ph = abs(ptA[i] - 0.5f) * 2f
                val baseR = ar * (1f - ph) + br0 * ph
                val baseG = ag * (1f - ph) + bg0 * ph
                val baseB = ab * (1f - ph) + bb0 * ph
                // Glanz: weniger weiß, besonders bei Ringen weiter hinten
                val bright = 0.62f + 0.38f * lit
                val spec = smooth(0.65f, 1f, lit) * 0.18f * max(0.3f, 1f - 0.5f * c[H])
                val cr = min(255f, baseR * bright + 255f * spec).toInt()
                val cg = min(255f, baseG * bright + 255f * spec).toInt()
                val cb = min(255f, baseB * bright + 255f * spec).toInt()

                val wpx = max(
                    1f,
                    uwEff * 0.1f * scale * (sclA[i] + sclA[j]) * 0.5f * screenW * 0.5f * lineWidthScale
                )

                // Schein an hellen Stellen
                if (glowStrength > 0f && lit > 0.6f) {
                    // Schein wird stärker, je weiter der Startbildschirm von der Mitte entfernt ist
                    val g = 0.035f * smooth(0.6f, 0.9f, lit) * alpha * glowStrength * (1f + 1.5f * abs(camC0))
                    linePaint.strokeCap = Paint.Cap.ROUND
                    drawSeg(canvas, i, cr, cg, cb, g, max(2f, wpx * 2f))
                    drawSeg(canvas, i, cr, cg, cb,  0.5f * g * (1 - g), max(2f, wpx * 3f))
                    drawSeg(canvas, i, cr, cg, cb,  0.9f * g * (1 - g), max(2f, wpx * 4f))
                    linePaint.strokeCap = Paint.Cap.BUTT
                }
                // Band mit weichem Rand: breit und blass, schmal und deckend
                drawSeg(canvas, i, cr, cg, cb, alpha * 0.35f, wpx)
                drawSeg(canvas, i, cr, cg, cb, alpha * 0.7f, max(1f, wpx * 0.55f))
                drawSeg(canvas, i, cr, cg, cb, alpha, max(1f, wpx * 0.25f))
            }
        }

        private fun drawSeg(
            canvas: Canvas, i: Int, cr: Int, cg: Int, cb: Int, alpha: Float, width: Float
        ) {
            val a = (min(1f, alpha) * 255f).toInt()
            if (a <= 0) return
            val j = (i + 1) % TOTAL
            linePaint.color = Color.argb(a, cr, cg, cb)
            linePaint.strokeWidth = width
            canvas.drawLine(sxA[i], syA[i], sxA[j], syA[j], linePaint)
        }
    }
}
