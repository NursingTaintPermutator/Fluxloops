package com.example.fluxloops

import android.content.BroadcastReceiver
import android.content.Context
import android.content.Intent
import android.content.IntentFilter
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.LinearGradient
import android.graphics.Matrix
import android.graphics.Paint
import android.graphics.Path
import android.graphics.Shader
import android.graphics.SweepGradient
import android.os.Build
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.os.SystemClock
import android.service.wallpaper.WallpaperService
import android.util.Log
import android.view.Choreographer
import android.view.MotionEvent
import android.view.SurfaceHolder
import kotlin.math.abs
import kotlin.math.cos
import kotlin.math.exp
import kotlin.math.hypot
import kotlin.math.max
import kotlin.math.min
import kotlin.math.sin
import kotlin.math.sqrt

class LoopsWallpaperService : WallpaperService() {

    override fun onCreateEngine(): Engine = LoopsEngine()

    /**
     * Ein dünner Loop: fast kreisförmige Ellipse, oben links hell, unten rechts dunkel.
     * cx, cy: Ruhelage des Mittelpunkts (Anteil von Breite/Höhe)
     * r: Radius als Anteil der Breite, asp: Verhältnis Höhe/Breite der Ellipse
     * phiDeg: Richtung der hellen Seite (Winkel, y zeigt nach unten)
     * depth: Folgefaktor beim Wischen, fa/fb: Reibung beim Ausgleiten
     * introX/introY: Startversatz beim Entsperren (Anteil von Breite/Höhe), introT: Dauer in s
     * blurBase: Grundunschärfe des ganzen Loops (0 = scharf, 1 = sehr unscharf)
     * blurAmt/blurPos: zusätzliche Unschärfe an einer Stelle des Bogens (Position 0..1)
     */
    private class Loop(
        val cx: Float, val cy: Float, val r: Float, val asp: Float,
        val rotDeg: Float, val phiDeg: Float, val widthDp: Float,
        val hiColor: Int, val shColor: Int,
        val depth: Float, val fa: Float, val fb: Float,
        val introX: Float, val introY: Float, val introT: Float,
        val blurBase: Float, val blurAmt: Float, val blurPos: Float
    ) {
        var x = 0f   // Verschiebung durch Wischen (Pixel)
        var y = 0f
        var vx = 0f  // Geschwindigkeit in Pixel/s
        var vy = 0f
        var hiShader: Shader? = null
        var shShader: Shader? = null
    }

    inner class LoopsEngine : Engine(), Choreographer.FrameCallback {

        private val tag = "LoopsWP"

        // Hier einstellen: Liniendicke und Stärke des Scheins
        private val thicknessScale = 1.5f
        private val glowStrength = 1.0f

        // Rottöne wie bisher (hier ändern, wenn es anders aussehen soll)
        private val light = Color.parseColor("#D6A2A7")
        private val mid = Color.parseColor("#CD7588")
        private val dark = Color.parseColor("#B55D63")

        private val loops = listOf(
            Loop(1.02f, 0.44f, 0.60f, 1.05f, -8f, -130f, 2.6f, light, dark, 0.35f, 1.5f, 5f, 0.75f, 0.18f, 2.6f, 0.00f, 0.70f, 0.75f),
            Loop(1.05f, 0.43f, 0.64f, 1.00f, 5f, -140f, 2.0f, mid, dark, 0.30f, 1.8f, 5f, 0.65f, 0.12f, 2.3f, 0.15f, 0.60f, 0.30f),
            Loop(0.98f, 0.46f, 0.57f, 1.10f, -12f, -120f, 1.8f, light, mid, 0.24f, 2.2f, 5f, 0.50f, -0.05f, 1.8f, 0.00f, 0.80f, 0.80f),
            Loop(1.10f, 0.40f, 0.70f, 1.00f, 0f, -150f, 1.5f, light, dark, 0.18f, 2.6f, 5f, 0.35f, 0.10f, 1.2f, 0.35f, 0.50f, 0.50f),
            Loop(1.00f, 0.42f, 0.52f, 1.15f, 10f, -125f, 1.4f, mid, dark, 0.12f, 3.2f, 5f, 0.22f, -0.08f, 0.8f, 0.10f, 0.70f, 0.25f),
            Loop(1.08f, 0.47f, 0.66f, 1.05f, -4f, -135f, 1.1f, light, mid, 0.08f, 4.0f, 5f, 0.14f, 0.04f, 0.5f, 0.50f, 0.40f, 0.60f),
            Loop(0.95f, 0.45f, 0.46f, 1.20f, 15f, -115f, 1.6f, mid, dark, 0.05f, 5.0f, 5f, 0.08f, -0.03f, 0.35f, 0.20f, 0.70f, 0.70f)
        )

        private val steps = 48
        private val outX = FloatArray(steps + 1)
        private val outY = FloatArray(steps + 1)
        private val inX = FloatArray(steps + 1)
        private val inY = FloatArray(steps + 1)
        private val piF = Math.PI.toFloat()

        // Schichten pro Bogen: zwei Glow-Schichten hinten, dann der scharfe Kern
        private val layerGrow = floatArrayOf(2.2f, 1.1f, 0f)
        private val layerAlphaScale = floatArrayOf(0.08f, 0.15f, 1f)

        private val density = resources.displayMetrics.density
        private val bgPaint = Paint()
        private val loopPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply { style = Paint.Style.FILL }
        private val path = Path()
        private val shaderMatrix = Matrix()
        private val handler = Handler(Looper.getMainLooper())

        private var w = 1
        private var h = 1
        private var visible = false
        private var scheduled = false
        private var lastFrameNanos = 0L

        // Eingaben, die im nächsten Frame verarbeitet werden
        private var inDx = 0f
        private var inDy = 0f
        private var lastTouchX = 0f
        private var lastTouchY = 0f
        private var lastTouchMs = 0L

        // Position des Startbildschirms (für Launcher, die Offsets melden)
        private var prevXOff = 0f
        private var prevYOff = 0f
        private var haveOffset = false

        // Entsperr-Animation
        private var animStartMs = 0L
        private var pendingPush = false
        private var lastPushMs = 0L

        private val unlockReceiver = object : BroadcastReceiver() {
            override fun onReceive(context: Context, intent: Intent) {
                requestPush("Broadcast " + intent.action)
            }
        }

        init {
            // Farbverläufe mit Schärfeverlauf entlang des Bogens einmalig vorbereiten
            for (l in loops) {
                val phi = Math.toRadians(l.phiDeg.toDouble()).toFloat()
                l.hiShader = makeSweep(l, phi, l.hiColor, l.blurPos)
                l.shShader = makeSweep(l, phi + piF, l.shColor, 1f - l.blurPos)
            }
        }

        // Unschärfe (0..1) an der Stelle s (0..1) des Bogens
        private fun blurAt(l: Loop, s: Float, pos: Float): Float {
            val d = abs(s - pos) / 0.3f
            val bump = if (d >= 1f) 0f else (1f - d * d) * (1f - d * d)
            return min(1f, l.blurBase + l.blurAmt * bump)
        }

        // Farbverlauf um den Mittelpunkt: unscharfe Stellen werden blasser
        private fun makeSweep(l: Loop, midAngle: Float, color: Int, pos: Float): Shader {
            val n = 72
            val twoPi = 2f * piF
            val colors = IntArray(n + 1)
            for (i in 0..n) {
                val theta = twoPi * i / n
                var a = (theta - (midAngle - piF / 2f)) % twoPi
                if (a < 0f) a += twoPi
                val alpha = if (a <= piF) {
                    (255f * (1f - 0.65f * blurAt(l, a / piF, pos))).toInt()
                } else {
                    0
                }
                colors[i] = Color.argb(alpha, Color.red(color), Color.green(color), Color.blue(color))
            }
            return SweepGradient(0f, 0f, colors, null)
        }

        override fun onCreate(surfaceHolder: SurfaceHolder) {
            super.onCreate(surfaceHolder)
            setTouchEventsEnabled(true)
            val filter = IntentFilter().apply {
                addAction(Intent.ACTION_USER_PRESENT)
            }
            if (Build.VERSION.SDK_INT >= 33) {
                this@LoopsWallpaperService.registerReceiver(
                    unlockReceiver, filter, Context.RECEIVER_NOT_EXPORTED
                )
            } else {
                this@LoopsWallpaperService.registerReceiver(unlockReceiver, filter)
            }
            Log.d(tag, "Engine erstellt, Receiver registriert")
        }

        override fun onDestroy() {
            super.onDestroy()
            handler.removeCallbacksAndMessages(null)
            Choreographer.getInstance().removeFrameCallback(this)
            try {
                this@LoopsWallpaperService.unregisterReceiver(unlockReceiver)
            } catch (e: IllegalArgumentException) {
                // war nicht registriert
            }
        }

        override fun onCommand(
            action: String?, x: Int, y: Int, z: Int,
            extras: Bundle?, resultRequested: Boolean
        ): Bundle? {
            if (action == "android.wallpaper.wakingup") {
                requestPush("Command wakingup")
            }
            return super.onCommand(action, x, y, z, extras, resultRequested)
        }

        override fun onSurfaceChanged(
            holder: SurfaceHolder, format: Int, width: Int, height: Int
        ) {
            super.onSurfaceChanged(holder, format, width, height)
            w = max(1, width)
            h = max(1, height)
            bgPaint.shader = LinearGradient(
                0f, 0f, 0f, h.toFloat(),
                Color.parseColor("#1C0000"), Color.parseColor("#050000"),
                Shader.TileMode.CLAMP
            )
            drawFrame()
        }

        override fun onVisibilityChanged(visible: Boolean) {
            this.visible = visible
            Log.d(tag, "Sichtbarkeit: $visible, pendingPush=$pendingPush")
            if (visible) {
                lastFrameNanos = 0L
                requestFrame()
                if (pendingPush) {
                    handler.postDelayed({ startUnlockAnimation("nach Sichtbarwerden") }, 120)
                }
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

        // Launcher meldet die Seitenposition: die Loops laufen mit (horizontal und vertikal)
        override fun onOffsetsChanged(
            xOffset: Float, yOffset: Float,
            xOffsetStep: Float, yOffsetStep: Float,
            xPixelOffset: Int, yPixelOffset: Int
        ) {
            val dxOff = xOffset - prevXOff
            val dyOff = yOffset - prevYOff
            prevXOff = xOffset
            prevYOff = yOffset
            if (!haveOffset) {
                haveOffset = true
                return
            }
            // Wenn gerade echte Touch-Ereignisse ankommen, nicht doppelt zählen
            if (SystemClock.uptimeMillis() - lastTouchMs < 400) return

            val stepX = if (xOffsetStep > 0f && xOffsetStep < 1f) xOffsetStep else 0.25f
            val stepY = if (yOffsetStep > 0f && yOffsetStep < 1f) yOffsetStep else 1f
            val dx = -(dxOff / stepX) * w
            val dy = -(dyOff / stepY) * h
            inDx += min(w.toFloat(), max(-w.toFloat(), dx))
            inDy += min(h.toFloat(), max(-h.toFloat(), dy))
            requestFrame()
        }

        // Direkter Fingerzug, falls der Launcher Touch-Ereignisse weitergibt
        override fun onTouchEvent(event: MotionEvent) {
            when (event.actionMasked) {
                MotionEvent.ACTION_DOWN -> {
                    lastTouchX = event.x
                    lastTouchY = event.y
                    lastTouchMs = SystemClock.uptimeMillis()
                }
                MotionEvent.ACTION_MOVE -> {
                    inDx += event.x - lastTouchX
                    inDy += event.y - lastTouchY
                    lastTouchX = event.x
                    lastTouchY = event.y
                    lastTouchMs = SystemClock.uptimeMillis()
                    requestFrame()
                }
            }
        }

        // --- Entsperr-Animation -----------------------------------------------------

        private fun requestPush(reason: String) {
            Log.d(tag, "Push angefordert: $reason, sichtbar=$visible")
            if (visible) {
                startUnlockAnimation(reason)
            } else {
                pendingPush = true // wird beim Sichtbarwerden gestartet
            }
        }

        // Loops starten rechts außerhalb und laufen mit Ease-out an ihre Ruhelage
        private fun startUnlockAnimation(reason: String) {
            val now = SystemClock.uptimeMillis()
            if (now - lastPushMs < 2500) return // doppelte Auslöser zusammenfassen
            lastPushMs = now
            pendingPush = false
            animStartMs = now
            Log.d(tag, "Entsperr-Animation gestartet: $reason")
            requestFrame()
        }

        // 1 am Anfang, 0 am Ende (Ease-out kubisch)
        private fun animFactor(l: Loop, nowMs: Long): Float {
            if (animStartMs == 0L) return 0f
            val p = (nowMs - animStartMs) / 1000f / l.introT
            if (p >= 1f) return 0f
            val q = 1f - max(0f, p)
            return q * q * q
        }

        private fun animActive(nowMs: Long): Boolean {
            if (animStartMs == 0L) return false
            val t = (nowMs - animStartMs) / 1000f
            for (l in loops) if (t < l.introT) return true
            return false
        }

        // --- Animation --------------------------------------------------------------

        private fun requestFrame() {
            if (!visible || scheduled) return
            scheduled = true
            Choreographer.getInstance().postFrameCallback(this)
        }

        override fun doFrame(frameTimeNanos: Long) {
            scheduled = false
            if (!visible) return
            var dt = if (lastFrameNanos == 0L) 1f / 60f
            else (frameTimeNanos - lastFrameNanos) / 1_000_000_000f
            dt = min(max(dt, 1f / 240f), 1f / 30f)
            lastFrameNanos = frameTimeNanos

            var moving = step(dt)
            val now = SystemClock.uptimeMillis()
            if (animActive(now)) {
                moving = true
            } else if (animStartMs != 0L) {
                animStartMs = 0L
            }
            drawFrame()

            if (moving) {
                requestFrame()
            } else {
                lastFrameNanos = 0L // Ruhe: keine weiteren Frames, spart Akku
            }
        }

        private fun wMaxOf(l: Loop): Float = l.widthDp * density * thicknessScale
        private fun marginX(l: Loop): Float = l.r * w + wMaxOf(l) * 8f
        private fun marginY(l: Loop): Float = l.r * w * l.asp + wMaxOf(l) * 8f
        private fun periodX(l: Loop): Float = w + 2f * marginX(l)
        private fun periodY(l: Loop): Float = h + 2f * marginY(l)

        // Folgen beim Wischen, danach Ausgleiten mit Reibung (stark bei hohem Tempo, schwach bei niedrigem)
        private fun step(dt: Float): Boolean {
            val hasInput = inDx != 0f || inDy != 0f
            var moving = hasInput
            for (l in loops) {
                if (hasInput) {
                    val mx = inDx * l.depth
                    val my = inDy * l.depth * 0.6f
                    l.x += mx
                    l.y += my
                    l.vx = 0.5f * l.vx + 0.5f * (mx / dt)
                    l.vy = 0.5f * l.vy + 0.5f * (my / dt)
                    moving = true
                } else {
                    l.x += l.vx * dt
                    l.y += l.vy * dt
                    val speed = hypot(l.vx, l.vy) / w
                    val f = exp(-(l.fa + l.fb * speed) * dt)
                    l.vx *= f
                    l.vy *= f
                    if (hypot(l.vx, l.vy) > 3f) {
                        moving = true
                    } else {
                        l.vx = 0f
                        l.vy = 0f
                    }
                }
                l.x %= periodX(l)
                l.y %= periodY(l)
            }
            inDx = 0f
            inDy = 0f
            return moving
        }

        // --- Zeichnen ---------------------------------------------------------------

        private fun wrap(v: Float, period: Float, minValue: Float): Float {
            var r = (v - minValue) % period
            if (r < 0f) r += period
            return r + minValue
        }

        private fun drawFrame() {
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
                canvas.drawRect(0f, 0f, w.toFloat(), h.toFloat(), bgPaint)
                val now = SystemClock.uptimeMillis()
                for (l in loops) drawLoop(canvas, l, now)
            } finally {
                holder.unlockCanvasAndPost(canvas)
            }
        }

        private fun drawLoop(canvas: Canvas, l: Loop, nowMs: Long) {
            val rx = l.r * w
            val ry = rx * l.asp
            val wMax = wMaxOf(l)
            val f = animFactor(l, nowMs)
            val offX = l.introX * w * f
            val offY = l.introY * h * f
            // Mittelpunkt wandert weiter und kommt auf der Gegenseite wieder herein
            val cx = wrap(l.cx * w + l.x + offX, periodX(l), -marginX(l))
            val cy = wrap(l.cy * h + l.y + offY, periodY(l), -marginY(l))
            val rot = Math.toRadians(l.rotDeg.toDouble()).toFloat()
            val phi = Math.toRadians(l.phiDeg.toDouble()).toFloat()

            shaderMatrix.setRotate(l.rotDeg)
            shaderMatrix.postTranslate(cx, cy)

            // dunkle Seite zuerst, helle Seite darüber
            drawArc(canvas, l, l.shShader, cx, cy, rx, ry, rot, phi + piF, wMax * 0.75f, 1f - l.blurPos, 200, 0.7f)
            drawArc(canvas, l, l.hiShader, cx, cy, rx, ry, rot, phi, wMax, l.blurPos, 235, 1f)
        }

        // Ein Bogen in drei Schichten (Glow, Glow, Kern)
        private fun drawArc(
            canvas: Canvas, l: Loop, shader: Shader?,
            cx: Float, cy: Float, rx: Float, ry: Float, rot: Float,
            midAngle: Float, wMax: Float, pos: Float, coreAlpha: Int, glowScale: Float
        ) {
            if (shader == null) return
            shader.setLocalMatrix(shaderMatrix)
            loopPaint.shader = shader
            for (i in layerGrow.indices) {
                buildArc(l, cx, cy, rx, ry, rot, midAngle, wMax, layerGrow[i], pos)
                val a = if (layerGrow[i] == 0f) coreAlpha.toFloat()
                else 255f * layerAlphaScale[i] * glowStrength * glowScale
                loopPaint.alpha = min(255f, max(0f, a)).toInt()
                canvas.drawPath(path, loopPaint)
            }
        }

        // Halbkreisbogen um die Richtung midAngle; Dicke läuft an beiden Enden auf null aus.
        // grow = 0: Kern, grow > 0: Glow (breiter, an unscharfen Stellen noch breiter)
        private fun buildArc(
            l: Loop, cx: Float, cy: Float, rx: Float, ry: Float, rot: Float,
            midAngle: Float, wMax: Float, grow: Float, pos: Float
        ) {
            val cr = cos(rot)
            val sr = sin(rot)
            for (j in 0..steps) {
                val s = j.toFloat() / steps
                val th = midAngle - piF / 2f + piF * s
                val ct = cos(th)
                val st = sin(th)
                val px = rx * ct
                val py = ry * st
                var nx = ry * ct
                var ny = rx * st
                val len = hypot(nx, ny)
                nx /= len
                ny /= len

                val b = blurAt(l, s, pos)
                val widen = if (grow == 0f) 1f + 0.6f * b else 1f + grow * (0.7f + 2.2f * b)
                // Rundungsfehler an den Enden dürfen nicht negativ werden (sonst NaN)
                val sn = max(0f, sin(piF * s))
                val wd = wMax * sn * sqrt(sn) * widen

                val ox = px + nx * wd * 0.5f
                val oy = py + ny * wd * 0.5f
                val ix = px - nx * wd * 0.5f
                val iy = py - ny * wd * 0.5f

                outX[j] = cx + ox * cr - oy * sr
                outY[j] = cy + ox * sr + oy * cr
                inX[j] = cx + ix * cr - iy * sr
                inY[j] = cy + ix * sr + iy * cr
            }

            path.rewind()
            path.moveTo(outX[0], outY[0])
            for (j in 1..steps) path.lineTo(outX[j], outY[j])
            for (j in steps downTo 0) path.lineTo(inX[j], inY[j])
            path.close()
        }
    }
}