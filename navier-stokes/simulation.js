
const canvas = document.getElementById('fluid-canvas');
const ctx = canvas.getContext('2d');
const resetButton = document.getElementById('reset-button');

const restartButton = document.getElementById('restart-button');

const N = 64; // Grid size
const size = canvas.width = canvas.height = 400;
const iter = 4;
const scale = size / N;

function Fluid(dt, diffusion, viscosity) {
    this.dt = dt;
    this.diff = diffusion;
    this.visc = viscosity;

    this.s = new Float32Array(N * N).fill(0);
    this.density = new Float32Array(N * N).fill(0);

    this.Vx = new Float32Array(N * N).fill(0);
    this.Vy = new Float32Array(N * N).fill(0);

    this.Vx0 = new Float32Array(N * N).fill(0);
    this.Vy0 = new Float32Array(N * N).fill(0);
}

function IX(x, y) {
    return x + y * N;
}

Fluid.prototype.step = function () {
    let N = this.N;
    let visc = this.visc;
    let diff = this.diff;
    let dt = this.dt;
    let Vx = this.Vx;
    let Vy = this.Vy;
    let Vx0 = this.Vx0;
    let Vy0 = this.Vy0;
    let s = this.s;
    let density = this.density;

    diffuse(1, Vx0, Vx, visc, dt, iter);
    diffuse(2, Vy0, Vy, visc, dt, iter);

    project(Vx0, Vy0, Vx, Vy, iter);

    advect(1, Vx, Vx0, Vx0, Vy0, dt);
    advect(2, Vy, Vy0, Vx0, Vy0, dt);

    project(Vx, Vy, Vx0, Vy0, iter);

    diffuse(0, s, density, diff, dt, iter);
    advect(0, density, s, Vx, Vy, dt);
}

Fluid.prototype.addDensity = function (x, y, amount) {
    this.density[IX(x, y)] += amount;
}

Fluid.prototype.addVelocity = function (x, y, amountX, amountY) {
    let index = IX(x, y);
    this.Vx[index] += amountX;
    this.Vy[index] += amountY;
}

function set_bnd(b, x) {
    for (let i = 1; i < N - 1; i++) {
        x[IX(i, 0)] = b === 2 ? -x[IX(i, 1)] : x[IX(i, 1)];
        x[IX(i, N - 1)] = b === 2 ? -x[IX(i, N - 2)] : x[IX(i, N - 2)];
    }
    for (let j = 1; j < N - 1; j++) {
        x[IX(0, j)] = b === 1 ? -x[IX(1, j)] : x[IX(1, j)];
        x[IX(N - 1, j)] = b === 1 ? -x[IX(N - 2, j)] : x[IX(N - 2, j)];
    }

    x[IX(0, 0)] = 0.5 * (x[IX(1, 0)] + x[IX(0, 1)]);
    x[IX(0, N - 1)] = 0.5 * (x[IX(1, N - 1)] + x[IX(0, N - 2)]);
    x[IX(N - 1, 0)] = 0.5 * (x[IX(N - 2, 0)] + x[IX(N - 1, 1)]);
    x[IX(N - 1, N - 1)] = 0.5 * (x[IX(N - 2, N - 1)] + x[IX(N - 1, N - 2)]);
}

function lin_solve(b, x, x0, a, c, iter) {
    let cRecip = 1.0 / c;
    for (let k = 0; k < iter; k++) {
        for (let j = 1; j < N - 1; j++) {
            for (let i = 1; i < N - 1; i++) {
                x[IX(i, j)] =
                    (x0[IX(i, j)] +
                        a * (x[IX(i + 1, j)] + x[IX(i - 1, j)] + x[IX(i, j + 1)] + x[IX(i, j - 1)])) *
                    cRecip;
            }
        }
        set_bnd(b, x);
    }
}

function diffuse(b, x, x0, diff, dt, iter) {
    let a = dt * diff * (N - 2) * (N - 2);
    lin_solve(b, x, x0, a, 1 + 6 * a, iter);
}

function project(velocX, velocY, p, div, iter) {
    for (let j = 1; j < N - 1; j++) {
        for (let i = 1; i < N - 1; i++) {
            div[IX(i, j)] =
                (-0.5 *
                    (velocX[IX(i + 1, j)] -
                        velocX[IX(i - 1, j)] +
                        velocY[IX(i, j + 1)] -
                        velocY[IX(i, j - 1)])) /
                N;
            p[IX(i, j)] = 0;
        }
    }
    set_bnd(0, div);
    set_bnd(0, p);
    lin_solve(0, p, div, 1, 6, iter);

    for (let j = 1; j < N - 1; j++) {
        for (let i = 1; i < N - 1; i++) {
            velocX[IX(i, j)] -= 0.5 * (p[IX(i + 1, j)] - p[IX(i - 1, j)]) * N;
            velocY[IX(i, j)] -= 0.5 * (p[IX(i, j + 1)] - p[IX(i, j - 1)]) * N;
        }
    }
    set_bnd(1, velocX);
    set_bnd(2, velocY);
}

function advect(b, d, d0, velocX, velocY, dt) {
    let i0, i1, j0, j1;
    let dtx = dt * (N - 2);
    let dty = dt * (N - 2);
    let s0, s1, t0, t1;
    let tmp1, tmp2, x, y;
    let Nfloat = N - 2;
    let ifloat, jfloat;
    let i, j;

    for (j = 1, jfloat = 1; j < N - 1; j++, jfloat++) {
        for (i = 1, ifloat = 1; i < N - 1; i++, ifloat++) {
            tmp1 = dtx * velocX[IX(i, j)];
            tmp2 = dty * velocY[IX(i, j)];
            x = ifloat - tmp1;
            y = jfloat - tmp2;

            if (x < 0.5) x = 0.5;
            if (x > Nfloat + 0.5) x = Nfloat + 0.5;
            i0 = Math.floor(x);
            i1 = i0 + 1.0;
            if (y < 0.5) y = 0.5;
            if (y > Nfloat + 0.5) y = Nfloat + 0.5;
            j0 = Math.floor(y);
            j1 = j0 + 1.0;

            s1 = x - i0;
            s0 = 1.0 - s1;
            t1 = y - j0;
            t0 = 1.0 - t1;

            let i0i = parseInt(i0);
            let i1i = parseInt(i1);
            let j0i = parseInt(j0);
            let j1i = parseInt(j1);

            d[IX(i, j)] =
                s0 * (t0 * d0[IX(i0i, j0i)] + t1 * d0[IX(i0i, j1i)]) +
                s1 * (t0 * d0[IX(i1i, j0i)] + t1 * d0[IX(i1i, j1i)]);
        }
    }
    set_bnd(b, d);
}

let fluid = new Fluid(0.1, 0, 0.0000001);

function getColor(density) {
    // Clamp density to a 0-1 range for color mapping.
    // The initial density is high, so we'll cap it at 1000.
    let d = Math.max(0, Math.min(1000, density)) / 1000;

    let r, g, b;

    if (d < 0.5) {
        // From black (0) to red (0.5)
        r = d * 2 * 255;
        g = 0;
        b = 0;
    } else {
        // From red (0.5) to yellow (1.0)
        r = 255;
        g = (d - 0.5) * 2 * 255;
        b = 0;
    }
    
    // Add white for very high densities (d > 0.9)
    if (d > 0.9) {
        let whiteAmount = (d - 0.9) / 0.1;
        r = 255;
        g = 255;
        b = whiteAmount * 255;
    }


    return `rgb(${Math.floor(r)}, ${Math.floor(g)}, ${Math.floor(b)})`;
}

function render() {
    ctx.clearRect(0, 0, size, size);
    fluid.step();
    let density = fluid.density;
    for (let i = 0; i < N; i++) {
        for (let j = 0; j < N; j++) {
            let d = density[IX(i, j)];
            ctx.fillStyle = getColor(d);
            ctx.fillRect(i * scale, j * scale, scale, scale);
        }
    }
}

function reset() {
    fluid = new Fluid(0.1, 0, 0.0000001);
    setupInitialConditions();
}

function restart() {
    // Clear existing density and velocity
    fluid.density.fill(0);
    fluid.Vx.fill(0);
    fluid.Vy.fill(0);
    fluid.Vx0.fill(0);
    fluid.Vy0.fill(0);
    setupInitialConditions();
}


resetButton.addEventListener('click', reset);
restartButton.addEventListener('click', restart);

let then = Date.now();
function animate() {
    requestAnimationFrame(animate);
    let now = Date.now();
    let delta = now - then;
    if (delta > 1000/30){ // cap at 30fps
        then = now;
        render();
    }
}

// Mouse interaction
let mouseX = 0;
let mouseY = 0;
let pmouseX = 0;
let pmouseY = 0;
let isDragging = false;

canvas.addEventListener('mousedown', (e) => {
    isDragging = true;
    mouseX = e.offsetX;
    mouseY = e.offsetY;
});

canvas.addEventListener('mousemove', (e) => {
    pmouseX = mouseX;
    pmouseY = mouseY;
    mouseX = e.offsetX;
    mouseY = e.offsetY;
    if (isDragging) {
        let x = Math.floor(mouseX / scale);
        let y = Math.floor(mouseY / scale);
        let amountX = mouseX - pmouseX;
        let amountY = mouseY - pmouseY;
        fluid.addDensity(x, y, 100);
        fluid.addVelocity(x, y, amountX, amountY);
    }
});

canvas.addEventListener('mouseup', () => {
    isDragging = false;
});

function setupInitialConditions() {
    // This setup creates two opposing jets of fluid that will collide in the center.
    const center = Math.floor(N / 2);
    const offset = Math.floor(N / 4);

    // Jet 1 (from the left)
    for (let y = center - 5; y < center + 5; y++) {
        fluid.addDensity(offset, y, 1000);
        fluid.addVelocity(offset, y, 10, 0);
    }

    // Jet 2 (from the right)
    for (let y = center - 5; y < center + 5; y++) {
        fluid.addDensity(N - offset, y, 1000);
        fluid.addVelocity(N - offset, y, -10, 0);
    }
}

setupInitialConditions();
animate();
