import { OrbitControls } from 'https://cdn.skypack.dev/three@0.128.0/examples/jsm/controls/OrbitControls.js';

// --- Basic Three.js Setup ---
const scene = new THREE.Scene();
const camera = new THREE.PerspectiveCamera(75, window.innerWidth / window.innerHeight, 0.1, 1000);
const renderer = new THREE.WebGLRenderer();
renderer.setSize(window.innerWidth, window.innerHeight);
document.body.appendChild(renderer.domElement);

const controls = new OrbitControls(camera, renderer.domElement);
camera.position.z = 5;
controls.update();

window.addEventListener('resize', () => {
    renderer.setSize(window.innerWidth, window.innerHeight);
    camera.aspect = window.innerWidth / window.innerHeight;
    camera.updateProjectionMatrix();
});

// --- Fluid Simulation Code (Adapted for 3D) ---
const N = 60; // Increased grid size
const iter = 8;

function IX(x, y, z) {
    return x + y * N + z * N * N;
}

class Fluid {
    constructor(dt, diffusion, viscosity) {
        this.dt = dt;
        this.diff = diffusion;
        this.visc = viscosity;

        this.s = new Float32Array(N * N * N).fill(0);
        this.density = new Float32Array(N * N * N).fill(0);

        this.Vx = new Float32Array(N * N * N).fill(0);
        this.Vy = new Float32Array(N * N * N).fill(0);
        this.Vz = new Float32Array(N * N * N).fill(0);

        this.Vx0 = new Float32Array(N * N * N).fill(0);
        this.Vy0 = new Float32Array(N * N * N).fill(0);
        this.Vz0 = new Float32Array(N * N * N).fill(0);
    }

    addDensity(x, y, z, amount) {
        if (x < 0 || x >= N || y < 0 || y >= N || z < 0 || z >= N) return;
        this.density[IX(x, y, z)] += amount;
    }

    addVelocity(x, y, z, amountX, amountY, amountZ) {
        if (x < 0 || x >= N || y < 0 || y >= N || z < 0 || z >= N) return;
        const index = IX(x, y, z);
        this.Vx[index] += amountX;
        this.Vy[index] += amountY;
        this.Vz[index] += amountZ;
    }
    
    step() {
        let visc = this.visc;
        let diff = this.diff;
        let dt = this.dt;
        let Vx = this.Vx;
        let Vy = this.Vy;
        let Vz = this.Vz;
        let Vx0 = this.Vx0;
        let Vy0 = this.Vy0;
        let Vz0 = this.Vz0;
        let s = this.s;
        let density = this.density;

        diffuse(1, Vx0, Vx, visc, dt, iter);
        diffuse(2, Vy0, Vy, visc, dt, iter);
        diffuse(3, Vz0, Vz, visc, dt, iter);

        project(Vx0, Vy0, Vz0, Vx, Vy, iter);

        advect(1, Vx, Vx0, Vx0, Vy0, Vz0, dt);
        advect(2, Vy, Vy0, Vx0, Vy0, Vz0, dt);
        advect(3, Vz, Vz0, Vx0, Vy0, Vz0, dt);

        project(Vx, Vy, Vz, Vx0, Vy0, iter);

        diffuse(0, s, density, diff, dt, iter);
        advect(0, density, s, Vx, Vy, Vz, dt);
    }
}

function set_bnd(b, x) {
    for (let j = 1; j < N - 1; j++) {
        for (let i = 1; i < N - 1; i++) {
            x[IX(i, j, 0)] = b === 3 ? -x[IX(i, j, 1)] : x[IX(i, j, 1)];
            x[IX(i, j, N - 1)] = b === 3 ? -x[IX(i, j, N - 2)] : x[IX(i, j, N - 2)];
        }
    }
    for (let k = 1; k < N - 1; k++) {
        for (let i = 1; i < N - 1; i++) {
            x[IX(i, 0, k)] = b === 2 ? -x[IX(i, 1, k)] : x[IX(i, 1, k)];
            x[IX(i, N - 1, k)] = b === 2 ? -x[IX(i, N - 2, k)] : x[IX(i, N - 2, k)];
        }
    }
    for (let k = 1; k < N - 1; k++) {
        for (let j = 1; j < N - 1; j++) {
            x[IX(0, j, k)] = b === 1 ? -x[IX(1, j, k)] : x[IX(1, j, k)];
            x[IX(N - 1, j, k)] = b === 1 ? -x[IX(N - 2, j, k)] : x[IX(N - 2, j, k)];
        }
    }

    x[IX(0, 0, 0)] = (x[IX(1, 0, 0)] + x[IX(0, 1, 0)] + x[IX(0, 0, 1)]) / 3;
    // ... (and so on for all 8 corners)
}

function lin_solve(b, x, x0, a, c, iter) {
    let cRecip = 1.0 / c;
    for (let k = 0; k < iter; k++) {
        for (let m = 1; m < N - 1; m++) {
            for (let j = 1; j < N - 1; j++) {
                for (let i = 1; i < N - 1; i++) {
                    x[IX(i, j, m)] =
                        (x0[IX(i, j, m)] +
                            a * (x[IX(i + 1, j, m)] + x[IX(i - 1, j, m)] +
                                 x[IX(i, j + 1, m)] + x[IX(i, j - 1, m)] +
                                 x[IX(i, j, m + 1)] + x[IX(i, j, m - 1)])) *
                        cRecip;
                }
            }
        }
        set_bnd(b, x);
    }
}

function diffuse(b, x, x0, diff, dt, iter) {
    let a = dt * diff * (N - 2) * (N - 2);
    lin_solve(b, x, x0, a, 1 + 6 * a, iter);
}

function project(velocX, velocY, velocZ, p, div, iter) {
    for (let k = 1; k < N - 1; k++) {
        for (let j = 1; j < N - 1; j++) {
            for (let i = 1; i < N - 1; i++) {
                div[IX(i, j, k)] = -0.5 * (
                    velocX[IX(i + 1, j, k)] - velocX[IX(i - 1, j, k)] +
                    velocY[IX(i, j + 1, k)] - velocY[IX(i, j - 1, k)] +
                    velocZ[IX(i, j, k + 1)] - velocZ[IX(i, j, k - 1)]
                ) / N;
                p[IX(i, j, k)] = 0;
            }
        }
    }
    set_bnd(0, div);
    set_bnd(0, p);
    lin_solve(0, p, div, 1, 6, iter);

    for (let k = 1; k < N - 1; k++) {
        for (let j = 1; j < N - 1; j++) {
            for (let i = 1; i < N - 1; i++) {
                velocX[IX(i, j, k)] -= 0.5 * (p[IX(i + 1, j, k)] - p[IX(i - 1, j, k)]) * N;
                velocY[IX(i, j, k)] -= 0.5 * (p[IX(i, j + 1, k)] - p[IX(i, j - 1, k)]) * N;
                velocZ[IX(i, j, k)] -= 0.5 * (p[IX(i, j, k + 1)] - p[IX(i, j, k - 1)]) * N;
            }
        }
    }
    set_bnd(1, velocX);
    set_bnd(2, velocY);
    set_bnd(3, velocZ);
}

function advect(b, d, d0, velocX, velocY, velocZ, dt) {
    let i0, i1, j0, j1, k0, k1;
    let dtx = dt * (N - 2);
    let dty = dt * (N - 2);
    let dtz = dt * (N - 2);
    let s0, s1, t0, t1, u0, u1;
    let tmp1, tmp2, tmp3, x, y, z;
    let Nfloat = N - 2;
    let ifloat, jfloat, kfloat;
    let i, j, k;

    for (k = 1, kfloat = 1; k < N - 1; k++, kfloat++) {
        for (j = 1, jfloat = 1; j < N - 1; j++, jfloat++) {
            for (i = 1, ifloat = 1; i < N - 1; i++, ifloat++) {
                tmp1 = dtx * velocX[IX(i, j, k)];
                tmp2 = dty * velocY[IX(i, j, k)];
                tmp3 = dtz * velocZ[IX(i, j, k)];
                x = ifloat - tmp1;
                y = jfloat - tmp2;
                z = kfloat - tmp3;

                if (x < 0.5) x = 0.5;
                if (x > Nfloat + 0.5) x = Nfloat + 0.5;
                i0 = Math.floor(x);
                i1 = i0 + 1.0;
                if (y < 0.5) y = 0.5;
                if (y > Nfloat + 0.5) y = Nfloat + 0.5;
                j0 = Math.floor(y);
                j1 = j0 + 1.0;
                if (z < 0.5) z = 0.5;
                if (z > Nfloat + 0.5) z = Nfloat + 0.5;
                k0 = Math.floor(z);
                k1 = k0 + 1.0;
                
                s1 = x - i0; s0 = 1.0 - s1;
                t1 = y - j0; t0 = 1.0 - t1;
                u1 = z - k0; u0 = 1.0 - u1;

                d[IX(i, j, k)] =
                    s0 * (t0 * (u0 * d0[IX(i0, j0, k0)] + u1 * d0[IX(i0, j0, k1)]) +
                          t1 * (u0 * d0[IX(i0, j1, k0)] + u1 * d0[IX(i0, j1, k1)])) +
                    s1 * (t0 * (u0 * d0[IX(i1, j0, k0)] + u1 * d0[IX(i1, j0, k1)]) +
                          t1 * (u0 * d0[IX(i1, j1, k0)] + u1 * d0[IX(i1, j1, k1)]));
            }
        }
    }
    set_bnd(b, d);
}

let fluid = new Fluid(0.1, 0, 0.0000001);

// --- Visualization ---
const worldSize = 4;
const voxelSize = worldSize / N;
const geometry = new THREE.BoxGeometry(voxelSize, voxelSize, voxelSize);
const material = new THREE.MeshBasicMaterial({
    color: 0xffffff,
    transparent: true,
    opacity: 0.8,
    blending: THREE.AdditiveBlending,
    depthWrite: false
});

const instanceCount = N * N * N;
const instanceMesh = new THREE.InstancedMesh(geometry, material, instanceCount);
instanceMesh.instanceMatrix.setUsage(THREE.DynamicDrawUsage);
scene.add(instanceMesh);

const dummy = new THREE.Object3D();

function getColor(density) {
    let d = Math.max(0, Math.min(100, density)) / 100;
    const color = new THREE.Color();
    // Blue-ish to White thermal map style
    color.setHSL(0.6 - d * 0.5, 1.0, 0.2 + d * 0.8); 
    return color;
}

function updateVisuals() {
    let index = 0;
    for (let k = 0; k < N; k++) {
        for (let j = 0; j < N; j++) {
            for (let i = 0; i < N; i++) {
                const density = fluid.density[index];
                
                // Position
                dummy.position.set(
                    (i - N / 2) * voxelSize,
                    (j - N / 2) * voxelSize,
                    (k - N / 2) * voxelSize
                );

                // Scale based on density (cull empty cells)
                if (density > 0.1) {
                    let s = Math.min(density / 50, 1.2); // Cap scale
                    dummy.scale.set(s, s, s);
                    dummy.updateMatrix();
                    instanceMesh.setMatrixAt(index, dummy.matrix);
                    instanceMesh.setColorAt(index, getColor(density));
                } else {
                     // Hide empty cells by scaling to 0
                    dummy.scale.set(0, 0, 0);
                    dummy.updateMatrix();
                    instanceMesh.setMatrixAt(index, dummy.matrix);
                }
                
                index++;
            }
        }
    }
    instanceMesh.instanceMatrix.needsUpdate = true;
    if (instanceMesh.instanceColor) instanceMesh.instanceColor.needsUpdate = true;
}


function setupInitialConditions() {
    const center = Math.floor(N / 2);
    fluid.addDensity(center, center, 2, 500);
    fluid.addVelocity(center, center, 2, 0, 0, 5);
}

function reset() {
    fluid = new Fluid(0.1, 0, 0.0000001);
    setupInitialConditions();
}

document.getElementById('reset-button-3d').addEventListener('click', reset);

// --- Animation Loop ---
const jetVxInput = document.getElementById('jet-vx');
const jetVyInput = document.getElementById('jet-vy');
const jetVzInput = document.getElementById('jet-vz');

function animate() {
    requestAnimationFrame(animate);

    // Add density and velocity over time
    const center = Math.floor(N / 2);
    
    const vx = parseFloat(jetVxInput.value);
    const vy = parseFloat(jetVyInput.value);
    const vz = parseFloat(jetVzInput.value);

    fluid.addDensity(center, 5, center, 100);
    fluid.addVelocity(center, 5, center, vx, vy, vz);

    fluid.step();
    updateVisuals();
    controls.update();
    renderer.render(scene, camera);
}

reset();
animate();
