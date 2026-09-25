// Disk galaxy rotation simulation: dark matter halo vs. visible matter only.
//
// Each star moves on a circular orbit with angular speed omega(r) = v(r) / r.
// The two galaxies share identical initial conditions; only the rotation
// curve v(r) differs. Units are arbitrary but internally consistent:
// radius in kiloparsec-ish units (disk edge ~ 20), speed in ~km/s-ish units.

(function () {
  "use strict";

  // ---------------------------------------------------------------------
  // Physics: rotation curves
  // ---------------------------------------------------------------------

  const G = 1; // folded into the mass normalizations below

  // Visible matter: central bulge + exponential disk.
  const BULGE_MASS = 9000;
  const BULGE_SCALE = 1.2;     // Plummer softening radius
  const DISK_MASS = 26000;
  const DISK_SCALE = 4.0;      // exponential scale length

  // Dark matter: pseudo-isothermal halo. Density rho ~ 1/(1 + (r/rc)^2)
  // gives v_halo^2 = V_INF^2 * (1 - (rc/r) * atan(r/rc)), which rises and
  // then stays flat — exactly the behavior seen in observed rotation curves.
  const HALO_V_INF = 62;
  const HALO_CORE = 3.5;

  const MAX_RADIUS = 22;       // edge of the stellar disk

  // Enclosed visible mass at radius r (Plummer bulge + exponential disk).
  function visibleMassEnclosed(r) {
    const bulge = BULGE_MASS * Math.pow(r, 3) /
      Math.pow(r * r + BULGE_SCALE * BULGE_SCALE, 1.5);
    const x = r / DISK_SCALE;
    const disk = DISK_MASS * (1 - (1 + x) * Math.exp(-x));
    return bulge + disk;
  }

  function vVisible(r) {
    if (r <= 0) return 0;
    return Math.sqrt(G * visibleMassEnclosed(r) / r);
  }

  function vHalo(r, haloStrength) {
    if (r <= 0) return 0;
    const x = r / HALO_CORE;
    const v2 = HALO_V_INF * HALO_V_INF * (1 - Math.atan(x) / x);
    return haloStrength * Math.sqrt(Math.max(v2, 0));
  }

  function vTotal(r, haloStrength) {
    const vv = vVisible(r);
    const vh = vHalo(r, haloStrength);
    return Math.sqrt(vv * vv + vh * vh);
  }

  // ---------------------------------------------------------------------
  // Star field: shared initial conditions for both galaxies
  // ---------------------------------------------------------------------

  const STAR_COUNT = 5000;
  const SPIRAL_ARMS = 2;
  const SPIRAL_WIND = 0.28;    // radians of arm twist per radius unit
  const TIME_SCALE = 0.004;    // sim time per ms at speed 1

  // Each star: base radius and base angle. Per-galaxy state is just the
  // accumulated rotation angle, derived from omega(r) * t — circular orbits
  // never need integration, so the simulation is exact and drift-free.
  let stars = [];

  function makeStars() {
    stars = [];
    for (let i = 0; i < STAR_COUNT; i++) {
      // Exponential-ish surface density via rejection sampling.
      let r;
      do {
        r = -DISK_SCALE * 1.6 * Math.log(1 - Math.random());
      } while (r > MAX_RADIUS || r < 0.3);

      // Seed a two-armed logarithmic spiral so pattern shearing is visible.
      const arm = (Math.floor(Math.random() * SPIRAL_ARMS) / SPIRAL_ARMS) *
        Math.PI * 2;
      const scatter = (Math.random() + Math.random() + Math.random() - 1.5) * 0.55;
      const theta = arm + r * SPIRAL_WIND + scatter;

      stars.push({
        r: r,
        theta0: theta,
        size: Math.random() < 0.12 ? 1.6 : 1.0,
      });
    }
  }

  // ---------------------------------------------------------------------
  // Rendering
  // ---------------------------------------------------------------------

  const dmCanvas = document.getElementById("galaxyDM");
  const noDmCanvas = document.getElementById("galaxyNoDM");
  const curveCanvas = document.getElementById("curvePlot");
  const dmCtx = dmCanvas.getContext("2d");
  const noDmCtx = noDmCanvas.getContext("2d");
  const curveCtx = curveCanvas.getContext("2d");

  const speedSlider = document.getElementById("speed");
  const haloSlider = document.getElementById("halo");
  const pauseBtn = document.getElementById("pauseBtn");
  const resetBtn = document.getElementById("resetBtn");

  let simTime = 0;
  let paused = false;
  let lastFrame = null;

  // Color stars by orbital speed: slow = dim blue, fast = bright warm white.
  const V_COLOR_MAX = 95;
  function starColor(v, size) {
    const t = Math.min(v / V_COLOR_MAX, 1);
    const rCol = Math.round(110 + 145 * t);
    const gCol = Math.round(130 + 110 * t);
    const bCol = Math.round(220 + 25 * t);
    const alpha = size > 1 ? 0.95 : 0.7;
    return `rgba(${rCol},${gCol},${bCol},${alpha})`;
  }

  function drawGalaxy(ctx, canvas, haloStrength) {
    const w = canvas.width;
    const h = canvas.height;
    const cx = w / 2;
    const cy = h / 2;
    const scale = (Math.min(w, h) / 2 - 8) / MAX_RADIUS;

    ctx.fillStyle = "#06080f";
    ctx.fillRect(0, 0, w, h);

    // Soft central bulge glow.
    const glow = ctx.createRadialGradient(cx, cy, 0, cx, cy, BULGE_SCALE * 3.5 * scale);
    glow.addColorStop(0, "rgba(255,235,200,0.55)");
    glow.addColorStop(0.5, "rgba(255,220,170,0.12)");
    glow.addColorStop(1, "rgba(255,220,170,0)");
    ctx.fillStyle = glow;
    ctx.fillRect(0, 0, w, h);

    for (let i = 0; i < stars.length; i++) {
      const s = stars[i];
      const v = vTotal(s.r, haloStrength);
      const omega = v / s.r;
      const theta = s.theta0 + omega * simTime;
      const x = cx + Math.cos(theta) * s.r * scale;
      const y = cy + Math.sin(theta) * s.r * scale;
      ctx.fillStyle = starColor(v, s.size);
      ctx.fillRect(x - s.size / 2, y - s.size / 2, s.size, s.size);
    }
  }

  // ---------------------------------------------------------------------
  // Rotation curve plot
  // ---------------------------------------------------------------------

  function drawCurvePlot(haloStrength) {
    const w = curveCanvas.width;
    const h = curveCanvas.height;
    const padL = 44, padR = 12, padT = 14, padB = 34;
    const plotW = w - padL - padR;
    const plotH = h - padT - padB;
    const vMax = 110;

    const ctx = curveCtx;
    ctx.fillStyle = "#06080f";
    ctx.fillRect(0, 0, w, h);

    const xOf = (r) => padL + (r / MAX_RADIUS) * plotW;
    const yOf = (v) => padT + plotH - (v / vMax) * plotH;

    // Grid and axes.
    ctx.strokeStyle = "#1c2440";
    ctx.lineWidth = 1;
    ctx.fillStyle = "#8a93b8";
    ctx.font = "11px sans-serif";
    ctx.textAlign = "right";
    for (let v = 0; v <= vMax; v += 25) {
      ctx.beginPath();
      ctx.moveTo(padL, yOf(v));
      ctx.lineTo(w - padR, yOf(v));
      ctx.stroke();
      ctx.fillText(String(v), padL - 6, yOf(v) + 4);
    }
    ctx.textAlign = "center";
    for (let r = 0; r <= MAX_RADIUS; r += 5) {
      ctx.beginPath();
      ctx.moveTo(xOf(r), padT);
      ctx.lineTo(xOf(r), padT + plotH);
      ctx.stroke();
      ctx.fillText(String(r), xOf(r), h - padB + 16);
    }
    ctx.fillText("radius (kpc)", padL + plotW / 2, h - 6);
    ctx.save();
    ctx.translate(12, padT + plotH / 2);
    ctx.rotate(-Math.PI / 2);
    ctx.fillText("speed (km/s)", 0, 0);
    ctx.restore();

    function plotCurve(fn, color, dashed) {
      ctx.strokeStyle = color;
      ctx.lineWidth = 2;
      ctx.setLineDash(dashed ? [5, 4] : []);
      ctx.beginPath();
      for (let i = 1; i <= 200; i++) {
        const r = (i / 200) * MAX_RADIUS;
        const x = xOf(r);
        const y = yOf(Math.min(fn(r), vMax));
        if (i === 1) ctx.moveTo(x, y); else ctx.lineTo(x, y);
      }
      ctx.stroke();
      ctx.setLineDash([]);
    }

    plotCurve((r) => vHalo(r, haloStrength), "#7a64d8", true);
    plotCurve(vVisible, "#ff8a5c", false);
    plotCurve((r) => vTotal(r, haloStrength), "#6ea8ff", false);
  }

  // ---------------------------------------------------------------------
  // Main loop and controls
  // ---------------------------------------------------------------------

  let lastHaloStrength = null;

  function frame(now) {
    if (lastFrame === null) lastFrame = now;
    const dt = Math.min(now - lastFrame, 100);
    lastFrame = now;

    if (!paused) {
      simTime += dt * TIME_SCALE * parseFloat(speedSlider.value);
    }

    const haloStrength = parseFloat(haloSlider.value);
    drawGalaxy(dmCtx, dmCanvas, haloStrength);
    drawGalaxy(noDmCtx, noDmCanvas, 0);
    if (haloStrength !== lastHaloStrength) {
      drawCurvePlot(haloStrength);
      lastHaloStrength = haloStrength;
    }

    requestAnimationFrame(frame);
  }

  pauseBtn.addEventListener("click", () => {
    paused = !paused;
    pauseBtn.textContent = paused ? "Resume" : "Pause";
  });

  resetBtn.addEventListener("click", () => {
    makeStars();
    simTime = 0;
  });

  makeStars();
  requestAnimationFrame(frame);
})();
