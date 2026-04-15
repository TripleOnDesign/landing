import * as THREE from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';
import { EffectComposer } from 'three/addons/postprocessing/EffectComposer.js';
import { RenderPass } from 'three/addons/postprocessing/RenderPass.js';
import { UnrealBloomPass } from 'three/addons/postprocessing/UnrealBloomPass.js';
import anime from 'animejs';
import { createNoise3D, createNoise4D } from 'simplex-noise';

let scene, camera, renderer, controls, clock;
let composer, bloomPass;

let particlesGeometry, particlesMaterial, particleSystem;
let currentPositions, sourcePositions, targetPositions, swarmPositions;
let particleSizes, particleOpacities, particleEffectStrengths;
let noise3D, noise4D;

let morphTimeline = null;
let isInitialized = false;
let isMorphing = false;

const CONFIG = {
    particleCount: 15000,
    shapeSize: 14,
    swarmDistanceFactor: 1.5,
    swirlFactor: 4.0,
    noiseFrequency: 0.1,
    noiseTimeScale: 0.04,
    noiseMaxStrength: 2.8,
    colorScheme: 'rainbow',
    morphDuration: 4000,
    particleSizeRange: [0.08, 0.25],
    starCount: 18000,
    bloomStrength: 1.3,
    bloomRadius: 0.5,
    bloomThreshold: 0.05,
    idleFlowStrength: 0.25,
    idleFlowSpeed: 0.08,
    idleRotationSpeed: 0.02,
    morphSizeFactor: 0.5,
    morphBrightnessFactor: 0.6
};

const SHAPES = [
    { name: 'DNA', generator: generateDNA },
    { name: 'Galaxy', generator: generateGalaxy },
    { name: 'Virus', generator: generateVirus },
    { name: 'Smile', generator: generateSmile }
];

const TITLES = [
    "TRIPLE ON DESIGN",
    "GRAPHIC ON",
    "SWITCH ON",
    "WORLD ON"
];
let currentShapeIndex = 0;

const morphState = { progress: 0.0 };

const COLOR_SCHEMES = {
    fire: { startHue: 0, endHue: 45, saturation: 0.95, lightness: 0.6 },
    neon: { startHue: 300, endHue: 180, saturation: 1.0, lightness: 0.65 },
    nature: { startHue: 90, endHue: 160, saturation: 0.85, lightness: 0.55 },
    rainbow: { startHue: 0, endHue: 360, saturation: 0.9, lightness: 0.6 }
};

const tempVec = new THREE.Vector3();
const sourceVec = new THREE.Vector3();
const targetVec = new THREE.Vector3();
const swarmVec = new THREE.Vector3();
const noiseOffset = new THREE.Vector3();
const flowVec = new THREE.Vector3();
const bezPos = new THREE.Vector3();
const swirlAxis = new THREE.Vector3();
const currentVec = new THREE.Vector3();

function generateSphere(count, size) {
    const points = new Float32Array(count * 3);
    const phi = Math.PI * (Math.sqrt(5) - 1);
    for (let i = 0; i < count; i++) {
        const y = 1 - (i / (count - 1)) * 2;
        const radius = Math.sqrt(1 - y * y);
        const theta = phi * i;
        const x = Math.cos(theta) * radius;
        const z = Math.sin(theta) * radius;
        points[i * 3] = x * size;
        points[i * 3 + 1] = y * size;
        points[i * 3 + 2] = z * size;
    }
    return points;
}
function generateCube(count, size) {
    const points = new Float32Array(count * 3);
    const halfSize = size / 2;
    for (let i = 0; i < count; i++) {
        const face = Math.floor(Math.random() * 6);
        const u = Math.random() * size - halfSize;
        const v = Math.random() * size - halfSize;
        switch (face) {
            case 0: points.set([halfSize, u, v], i * 3); break;
            case 1: points.set([-halfSize, u, v], i * 3); break;
            case 2: points.set([u, halfSize, v], i * 3); break;
            case 3: points.set([u, -halfSize, v], i * 3); break;
            case 4: points.set([u, v, halfSize], i * 3); break;
            case 5: points.set([u, v, -halfSize], i * 3); break;
        }
    }
    return points;
}
function generatePyramid(count, size) {
    const points = new Float32Array(count * 3);
    const halfBase = size / 2;
    const height = size * 1.2;
    const apex = new THREE.Vector3(0, height / 2, 0);
    const baseVertices = [
        new THREE.Vector3(-halfBase, -height / 2, -halfBase), new THREE.Vector3(halfBase, -height / 2, -halfBase),
        new THREE.Vector3(halfBase, -height / 2, halfBase), new THREE.Vector3(-halfBase, -height / 2, halfBase)
    ];
    const baseArea = size * size;
    const sideFaceHeight = Math.sqrt(Math.pow(height, 2) + Math.pow(halfBase, 2));
    const sideFaceArea = 0.5 * size * sideFaceHeight;
    const totalArea = baseArea + 4 * sideFaceArea;
    const baseWeight = baseArea / totalArea;
    const sideWeight = sideFaceArea / totalArea;
    for (let i = 0; i < count; i++) {
        const r = Math.random();
        let p = new THREE.Vector3(); let u, v;
        if (r < baseWeight) {
            u = Math.random(); v = Math.random();
            p.lerpVectors(baseVertices[0], baseVertices[1], u);
            const p2 = new THREE.Vector3().lerpVectors(baseVertices[3], baseVertices[2], u);
            p.lerp(p2, v);
        } else {
            const faceIndex = Math.floor((r - baseWeight) / sideWeight);
            const v1 = baseVertices[faceIndex]; const v2 = baseVertices[(faceIndex + 1) % 4];
            u = Math.random(); v = Math.random();
            if (u + v > 1) { u = 1 - u; v = 1 - v; }
            p.addVectors(v1, tempVec.subVectors(v2, v1).multiplyScalar(u));
            p.add(tempVec.subVectors(apex, v1).multiplyScalar(v));
        }
        points.set([p.x, p.y, p.z], i * 3);
    }
    return points;
}
function generateTorus(count, size) {
    const points = new Float32Array(count * 3);
    const R = size * 0.7; const r = size * 0.3;
    for (let i = 0; i < count; i++) {
        const theta = Math.random() * Math.PI * 2; const phi = Math.random() * Math.PI * 2;
        const x = (R + r * Math.cos(phi)) * Math.cos(theta);
        const y = r * Math.sin(phi);
        const z = (R + r * Math.cos(phi)) * Math.sin(theta);
        points[i * 3] = x; points[i * 3 + 1] = y; points[i * 3 + 2] = z;
    }
    return points;
}
function generateGalaxy(count, size) {
    const points = new Float32Array(count * 3);
    const arms = 4; const armWidth = 0.6; const bulgeFactor = 0.3;
    for (let i = 0; i < count; i++) {
        const t = Math.pow(Math.random(), 1.5); const radius = t * size;
        const armIndex = Math.floor(Math.random() * arms);
        const armOffset = (armIndex / arms) * Math.PI * 2;
        const rotationAmount = radius / size * 6; const angle = armOffset + rotationAmount;
        const spread = (Math.random() - 0.5) * armWidth * (1 - radius / size);
        const theta = angle + spread;
        const x = radius * Math.cos(theta); const z = radius * Math.sin(theta);
        const y = (Math.random() - 0.5) * size * 0.1 * (1 - radius / size * bulgeFactor);
        points[i * 3] = x; points[i * 3 + 1] = y; points[i * 3 + 2] = z;
    }
    return points;
}
function generateHeart(count, size) {
    const points = new Float32Array(count * 3);

    // Heart Prism/Pillow (Extruded 2D shape)
    // Formula:
    // x = 16 sin^3(t)
    // y = 13 cos(t) - 5 cos(2t) - 2 cos(3t) - cos(4t)

    // Scale factors - Increased size as requested
    const scale = size * 0.055;
    const depth = size * 0.6; // Thickness of the heart pillow

    let i = 0;
    while (i < count) {
        // Explicit parametric distribution method:
        // Pick t, pick r (0 to 1), pick z.

        const t = Math.random() * Math.PI * 2;

        // Distribution fix:
        // To avoid "split" look (dense center), we modify r distribution or add jitter.
        // The dense center comes from the parametric concentration near the axis.
        // We'll use a more uniform spread and add some jitter.
        const r = Math.sqrt(Math.random()); // Sqrt for uniform area

        // Parametric Heart
        const hx = 16 * Math.pow(Math.sin(t), 3);
        const hy = 13 * Math.cos(t) - 5 * Math.cos(2 * t) - 2 * Math.cos(3 * t) - Math.cos(4 * t);

        // Inner point
        let x = hx * r * scale;
        let y = hy * r * scale;

        // Jitter to diffuse center line
        const jitterAmount = size * 0.05;
        x += (Math.random() - 0.5) * jitterAmount;
        y += (Math.random() - 0.5) * jitterAmount;

        // Z thickness - rounded pillow profile
        const zThickness = depth * Math.sqrt(1 - r * r); // Elliptical profile
        const z = (Math.random() - 0.5) * 2 * zThickness;

        points[i * 3] = x;
        points[i * 3 + 1] = y;
        points[i * 3 + 2] = z;
        i++;
    }
    return points;
}

function generateSmile(count, size) {
    const points = new Float32Array(count * 3);
    const faceRadius = size * 0.9;

    // Limits
    const leftEyeC = { x: -size * 0.35, y: size * 0.25, r: size * 0.15 };

    // Wink Eye Arc (Right)
    const winkCenter = { x: size * 0.35, y: size * 0.15 };
    const winkRadius = size * 0.15;
    const winkThick = size * 0.04;
    const winkStart = Math.PI * 0.1;
    const winkEnd = Math.PI * 0.9;

    // Mouth Arc
    const mouthCenter = { x: 0, y: size * 0.2 };
    const mouthRadius = size * 0.6;
    const mouthThick = size * 0.05;
    const mouthStart = Math.PI * 1.25;
    const mouthEnd = Math.PI * 1.75;

    function dToArc(px, py, cx, cy, r, start, end) {
        const dx = px - cx;
        const dy = py - cy;
        const d = Math.sqrt(dx * dx + dy * dy);
        let angle = Math.atan2(dy, dx);
        if (angle < 0) angle += Math.PI * 2;

        if (angle >= start && angle <= end) {
            return Math.abs(d - r);
        }

        const sx = cx + r * Math.cos(start);
        const sy = cy + r * Math.sin(start);
        const ex = cx + r * Math.cos(end);
        const ey = cy + r * Math.sin(end);

        const d1 = Math.sqrt((px - sx) * (px - sx) + (py - sy) * (py - sy));
        const d2 = Math.sqrt((px - ex) * (px - ex) + (py - ey) * (py - ey));
        return Math.min(d1, d2);
    }

    let i = 0;
    let safety = 0;
    while (i < count) {
        if (safety++ > count * 200) {
            // Fill remaining with random points to avoid empty buffer
            if (i < count) {
                points[i * 3] = (Math.random() - 0.5) * size;
                points[i * 3 + 1] = (Math.random() - 0.5) * size;
                points[i * 3 + 2] = (Math.random() - 0.5) * size;
                i++;
            }
            continue;
        }

        // Generate on XY Plane
        const rx = (Math.random() - 0.5) * 2 * faceRadius;
        const ry = (Math.random() - 0.5) * 2 * faceRadius;
        const rzThickness = (Math.random() - 0.5) * size * 0.2;

        if (rx * rx + ry * ry > faceRadius * faceRadius) continue;

        const dLeft = Math.sqrt((rx - leftEyeC.x) ** 2 + (ry - leftEyeC.y) ** 2);
        if (dLeft < leftEyeC.r) continue;

        const dWink = dToArc(rx, ry, winkCenter.x, winkCenter.y, winkRadius, winkStart, winkEnd);
        if (dWink < winkThick) continue;

        const dMouth = dToArc(rx, ry, mouthCenter.x, mouthCenter.y, mouthRadius, mouthStart, mouthEnd);
        if (dMouth < mouthThick) continue;

        // Apply Rotation to face Front (User reported it was lying down)
        // If it was "lying down", it might have been perceived as XZ.
        // We ensure coordinates are X, Y (Vertical).
        // To be safe, we can tilt it back slightly to face camera better.
        // Or simply mapped: x->x, y->y, z->thickness.
        // If user says "rotate to face front", maybe they want it strictly vertical?
        // It IS strictly vertical here.

        points[i * 3] = rx;
        points[i * 3 + 1] = ry;
        points[i * 3 + 2] = rzThickness;
        i++;
    }
    return points;
}

function generateVirus(count, size) {
    const points = new Float32Array(count * 3);
    const radius = size * 0.6;
    const spikeLength = size * 0.3;
    const numSpikes = 20;

    // Pre-calculate spike directions
    const spikeDirs = [];
    const phi = Math.PI * (Math.sqrt(5) - 1);
    for (let i = 0; i < numSpikes; i++) {
        const y = 1 - (i / (numSpikes - 1)) * 2;
        const r = Math.sqrt(1 - y * y);
        const theta = phi * i;
        const x = Math.cos(theta) * r;
        const z = Math.sin(theta) * r;
        spikeDirs.push(new THREE.Vector3(x, y, z).normalize());
    }

    for (let i = 0; i < count; i++) {
        let x, y, z;
        const r = Math.random();

        if (r < 0.2) { // Spikes
            const spikeIdx = Math.floor(Math.random() * numSpikes);
            const dir = spikeDirs[spikeIdx];
            const dist = radius + Math.random() * spikeLength;
            const jitter = 0.1 * size * (1 - (dist - radius) / spikeLength);

            const bx = dir.x * dist;
            const by = dir.y * dist;
            const bz = dir.z * dist;

            x = bx + (Math.random() - 0.5) * jitter;
            y = by + (Math.random() - 0.5) * jitter;
            z = bz + (Math.random() - 0.5) * jitter;
        } else { // Core Sphere
            const u = Math.random();
            const v = Math.random();
            const theta = 2 * Math.PI * u;
            const phi = Math.acos(2 * v - 1);
            const r_sphere = radius * Math.cbrt(Math.random());
            x = r_sphere * Math.sin(phi) * Math.cos(theta);
            y = r_sphere * Math.sin(phi) * Math.sin(theta);
            z = r_sphere * Math.cos(phi);
        }

        points[i * 3] = x;
        points[i * 3 + 1] = y;
        points[i * 3 + 2] = z;
    }
    return points;
}

function generateDNA(count, size) {
    const points = new Float32Array(count * 3);
    const radius = size * 0.4;
    const height = size * 1.5;
    const turns = 4;
    const particlesPerStrand = count / 2;

    // 30 degrees in radians
    const angleZ = 30 * Math.PI / 180;
    const cosZ = Math.cos(angleZ);
    const sinZ = Math.sin(angleZ);

    for (let i = 0; i < count; i++) {
        const strand = i < particlesPerStrand ? 0 : 1;
        const t = (i % particlesPerStrand) / particlesPerStrand;
        const angle = t * Math.PI * 2 * turns + (strand * Math.PI);
        const x_raw = Math.cos(angle) * radius;
        const y_raw = (t - 0.5) * height;
        const z_raw = Math.sin(angle) * radius;
        const jitter = 0.5;

        // Rotate around Z axis
        const x = x_raw * cosZ - y_raw * sinZ;
        const y = x_raw * sinZ + y_raw * cosZ;
        const z = z_raw;

        points[i * 3] = x + (Math.random() - 0.5) * jitter;
        points[i * 3 + 1] = y + (Math.random() - 0.5) * jitter;
        points[i * 3 + 2] = z + (Math.random() - 0.5) * jitter;
    }
    return points;
}

function generateText(count, size, text) {
    const points = new Float32Array(count * 3);
    const canvas = document.createElement('canvas');
    const ctx = canvas.getContext('2d');
    const W = 500; const H = 200;
    canvas.width = W; canvas.height = H;

    ctx.fillStyle = '#000000';
    ctx.fillRect(0, 0, W, H);
    ctx.font = 'bold 100px Inter, sans-serif';
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    ctx.fillStyle = '#ffffff';
    ctx.fillText(text, W / 2, H / 2);

    const imageData = ctx.getImageData(0, 0, W, H).data;
    const validPixels = [];
    for (let y = 0; y < H; y += 2) {
        for (let x = 0; x < W; x += 2) {
            const index = (y * W + x) * 4;
            if (imageData[index] > 128) {
                const nx = (x / W - 0.5) * 2;
                const ny = -(y / H - 0.5) * 2;
                validPixels.push({ x: nx, y: ny });
            }
        }
    }

    if (validPixels.length === 0) return generateSphere(count, size);

    const isMobile = window.innerWidth <= 768;
    const scaleX = isMobile ? size * 0.75 : size * 1.5;
    const scaleY = isMobile ? size * 0.3 : size * 0.6;
    const scaleZ = size * 0.2;

    for (let i = 0; i < count; i++) {
        const pixel = validPixels[Math.floor(Math.random() * validPixels.length)];
        points[i * 3]     = pixel.x * scaleX;
        points[i * 3 + 1] = pixel.y * scaleY;
        points[i * 3 + 2] = (Math.random() - 0.5) * scaleZ;
    }
    return points;
}

function init() {
    if (document.getElementById('particleCanvas')) return;

    clock = new THREE.Clock();
    noise3D = createNoise3D(() => Math.random());
    noise4D = createNoise4D(() => Math.random());
    scene = new THREE.Scene();
    scene.fog = new THREE.FogExp2(0x000308, 0.03);

    camera = new THREE.PerspectiveCamera(70, window.innerWidth / window.innerHeight, 0.1, 1000);
    if (window.innerWidth <= 768) {
        camera.position.set(0, 8, 38);
    } else {
        camera.position.set(0, 8, 28);
    }

    renderer = new THREE.WebGLRenderer({ antialias: true, alpha: true, powerPreference: 'high-performance' });
    renderer.domElement.id = 'particleCanvas';
    renderer.setSize(window.innerWidth, window.innerHeight);
    renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));

    const heroSection = document.getElementById('hero');
    if (heroSection) {
        heroSection.appendChild(renderer.domElement);
    } else {
        document.body.appendChild(renderer.domElement);
    }
    renderer.toneMapping = THREE.ACESFilmicToneMapping;
    renderer.toneMappingExposure = 1.1;

    controls = new OrbitControls(camera, renderer.domElement);
    controls.enableDamping = true; controls.dampingFactor = 0.05;
    controls.minDistance = 5; controls.maxDistance = 80;
    controls.autoRotate = true; controls.autoRotateSpeed = 0.3;
    controls.enableZoom = false;
    renderer.domElement.style.touchAction = 'pan-y';

    if (window.innerWidth <= 768) {
        controls.target.set(0, -2.5, 0);
    }
    controls.update();

    scene.add(new THREE.AmbientLight(0x404060));
    const dirLight1 = new THREE.DirectionalLight(0xffffff, 1.5);
    dirLight1.position.set(15, 20, 10); scene.add(dirLight1);
    const dirLight2 = new THREE.DirectionalLight(0x88aaff, 0.9);
    dirLight2.position.set(-15, -10, -15); scene.add(dirLight2);

    setupPostProcessing();
    createStarfield();
    setupParticleSystem();

    window.addEventListener('resize', onWindowResize);
    heroSection.addEventListener('click', (e) => {
        if (!e.target.closest('#sidebar') && !e.target.closest('input') && !e.target.closest('a')) {
            onCanvasClick(e);
        }
    });

    // UI Event Listeners
    document.querySelectorAll('.color-option').forEach(option => {
        option.addEventListener('click', (e) => {
            e.stopPropagation();
            document.querySelectorAll('.color-option').forEach(o => o.classList.remove('active'));
            e.target.classList.add('active');
            CONFIG.colorScheme = e.target.dataset.scheme;
            updateColors();
        });
    });
    const activeColor = document.querySelector(`.color-option[data-scheme="${CONFIG.colorScheme}"]`);
    if (activeColor) activeColor.classList.add('active');

    // Shape Button Listeners
    document.querySelectorAll('.shape-btn').forEach(btn => {
        btn.addEventListener('click', (e) => {
            e.stopPropagation();
            const shapeName = e.currentTarget.dataset.shape;
            triggerMorphToShape(shapeName);

            // UI Update
            document.querySelectorAll('.shape-btn').forEach(b => b.classList.remove('active'));
            e.currentTarget.classList.add('active');
        });
    });

    // GIF Trigger → Local HTML Modal
    const modal = document.getElementById('codepen-modal');
    const modalContainer = document.getElementById('modal-codepen-container');
    const modalCloseBtn = document.getElementById('modal-close-btn');

    function openModal(file) {
        if (!modal || !modalContainer) return;
        modalContainer.innerHTML = `<iframe
            src="${file}"
            style="width:100%;height:100%;border:none;"
            allowfullscreen
            title="Preview"
        ></iframe>`;
        modal.classList.add('is-open');
    }

    function closeModal() {
        if (!modal) return;
        modal.classList.remove('is-open');
        if (modalContainer) modalContainer.innerHTML = '';
    }

    document.querySelectorAll('.gif-trigger').forEach(trigger => {
        trigger.addEventListener('click', (e) => {
            e.stopPropagation();
            const file = trigger.dataset.file;
            if (file) openModal(file);
        });
    });

    if (modalCloseBtn) {
        modalCloseBtn.addEventListener('click', closeModal);
    }

    // Close on backdrop click
    if (modal) {
        modal.addEventListener('click', (e) => {
            if (e.target === modal) closeModal();
        });
    }

    // Close on Escape key
    document.addEventListener('keydown', (e) => {
        if (e.key === 'Escape') closeModal();
    });


    const textInput = document.getElementById('text-morph-input');
    const morphBtn = document.getElementById('text-morph-btn');

    if (textInput && morphBtn) {
        morphBtn.addEventListener('click', (e) => {
            e.stopPropagation();
            const text = textInput.value.trim();
            if (text) triggerMorphToText(text);
        });
        textInput.addEventListener('keypress', (e) => {
            if (e.key === 'Enter') {
                e.stopPropagation();
                const text = textInput.value.trim();
                if (text) triggerMorphToText(text);
            }
        });
    }

    isInitialized = true;
    animate();
    console.log("Initialization complete.");
}

// New function to morph to a specific shape by name
function triggerMorphToShape(shapeName) {
    if (isMorphing) return;
    const shapeIndex = SHAPES.findIndex(s => s.name === shapeName);
    if (shapeIndex === -1) {
        console.warn("Shape not found:", shapeName);
        return;
    }

    // If we are already at this shape (and it's not a text morph state), we could return. 
    // But forcing re-morph might be nice effect. Let's allow it but check if it breaks anything.
    // Actually, distinct visual feedback is better.

    isMorphing = true; controls.autoRotate = false;
    console.log("Morphing to shape:", shapeName);

    updateTitle(shapeIndex);

    const infoEl = document.getElementById('info');
    if (infoEl) {
        infoEl.innerText = `Morphing...`;
        infoEl.style.textShadow = '0 0 8px rgba(255, 150, 50, 0.9)';
    }

    sourcePositions.set(currentPositions);

    // Update index
    currentShapeIndex = shapeIndex;
    const nextTargetPositions = targetPositions[currentShapeIndex];
    const centerOffsetAmount = CONFIG.shapeSize * CONFIG.swarmDistanceFactor;

    for (let i = 0; i < CONFIG.particleCount; i++) {
        const i3 = i * 3;
        sourceVec.fromArray(sourcePositions, i3); targetVec.fromArray(nextTargetPositions, i3);
        swarmVec.lerpVectors(sourceVec, targetVec, 0.5);
        const offsetDir = tempVec.set(noise3D(i * 0.05, 10, 10), noise3D(20, i * 0.05, 20), noise3D(30, 30, i * 0.05)).normalize();
        const distFactor = sourceVec.distanceTo(targetVec) * 0.1 + centerOffsetAmount;
        swarmVec.addScaledVector(offsetDir, distFactor * (0.5 + Math.random() * 0.8));
        swarmPositions[i3] = swarmVec.x; swarmPositions[i3 + 1] = swarmVec.y; swarmPositions[i3 + 2] = swarmVec.z;
    }

    morphState.progress = 0;
    if (morphTimeline) morphTimeline.pause();

    morphTimeline = anime({
        targets: morphState, progress: 1, duration: CONFIG.morphDuration, easing: 'cubicBezier(0.4, 0.0, 0.2, 1.0)',
        complete: () => {
            console.log("Morphing complete.");
            if (infoEl) {
                infoEl.innerText = `Shape: "${SHAPES[currentShapeIndex].name}"`;
                infoEl.style.textShadow = '0 0 5px rgba(0, 128, 255, 0.8)';
            }
            currentPositions.set(targetPositions[currentShapeIndex]);
            particlesGeometry.attributes.position.needsUpdate = true;
            particleEffectStrengths.fill(0.0);
            particlesGeometry.attributes.aEffectStrength.needsUpdate = true;
            sourcePositions.set(targetPositions[currentShapeIndex]);
            updateColors();
            isMorphing = false; controls.autoRotate = true;
        }
    });
}

function triggerMorphToText(text) {
    if (isMorphing) return;
    isMorphing = true; controls.autoRotate = false; console.log("Morphing to text:", text);

    const textInput = document.getElementById('text-morph-input');
    if (textInput) textInput.blur();

    if (window.innerWidth <= 768) {
        // Wait for keyboard to fully close, then restore viewport
        window.scrollTo(0, 0);
        setTimeout(() => {
            window.scrollTo(0, 0);
            onWindowResize();  // This sets target to (0, -2.5, 0) for mobile — keep it
            controls.update();
        }, 500);
        // Second pass to catch late viewport restoration on slow devices
        setTimeout(() => {
            onWindowResize();
            controls.update();
        }, 900);
    }

    const infoEl = document.getElementById('info');
    if (infoEl) {
        infoEl.innerText = `Morphing...`;
        infoEl.style.textShadow = '0 0 8px rgba(255, 150, 50, 0.9)';
    }

    sourcePositions.set(currentPositions);

    const newPositions = generateText(CONFIG.particleCount, CONFIG.shapeSize, text);

    // We treat this as a temporary target, not adding to SHAPES array permanent rotation
    const nextTargetPositions = newPositions;
    const centerOffsetAmount = CONFIG.shapeSize * CONFIG.swarmDistanceFactor;

    for (let i = 0; i < CONFIG.particleCount; i++) {
        const i3 = i * 3;
        sourceVec.fromArray(sourcePositions, i3); targetVec.fromArray(nextTargetPositions, i3);
        swarmVec.lerpVectors(sourceVec, targetVec, 0.5);
        const offsetDir = tempVec.set(noise3D(i * 0.05, 10, 10), noise3D(20, i * 0.05, 20), noise3D(30, 30, i * 0.05)).normalize();
        const distFactor = sourceVec.distanceTo(targetVec) * 0.1 + centerOffsetAmount;
        swarmVec.addScaledVector(offsetDir, distFactor * (0.5 + Math.random() * 0.8));
        swarmPositions[i3] = swarmVec.x; swarmPositions[i3 + 1] = swarmVec.y; swarmPositions[i3 + 2] = swarmVec.z;
    }

    // Update target positions for the animation loop
    targetPositions[0] = nextTargetPositions; // Overwrite a slot or handle differently. 
    // Simplified approach: Update 'currentShapeIndex' logic or just use a dedicated 'targetPositions' variable that the loop uses.
    // The existing loop uses targetPositions[currentShapeIndex]. Let's cheat a bit and update the current shape's target data or use a special mode.
    // Actually, let's just create a temporary entry in SHAPES or just override logic.
    // Better: Allow updateMorphAnimation to use a specific target array.

    // Hack: We will overwrite the targetPositions of the current index (or a temp index) for this operation.
    // But SHAPES is const. targetPositions is a let, but initialized as array of arrays.
    // specific implementation:
    // We'll replace the target data for the *next* morph in our logic.

    // Let's force currentShapeIndex to -1 or similar to indicate custom shape, or just update the targets.
    // Since SHAPES is used to cycle, text morphing breaks the cycle.

    // Let's store the text shape in a separate variable and update specific logic.
    // Easier way with existing code structure:
    // define a custom Target var.
    // But updateMorphAnimation uses targetPositions[currentShapeIndex].

    // So:
    // 1. Create a dummy shape in SHAPES for 'Text' if not exists, or handle custom target.
    // Let's just push it to targetPositions array dynamically.

    // Actually, `targetPositions` is initialized as:
    // targetPositions = SHAPES.map(...)

    // We can just add the new positions to `targetPositions` list and point `currentShapeIndex` to it.
    targetPositions.push(newPositions);
    currentShapeIndex = targetPositions.length - 1;
    SHAPES[currentShapeIndex] = { name: 'Text: ' + text }; // Mock object for labels

    morphState.progress = 0;
    if (morphTimeline) morphTimeline.pause();
    morphTimeline = anime({
        targets: morphState, progress: 1, duration: CONFIG.morphDuration, easing: 'cubicBezier(0.4, 0.0, 0.2, 1.0)',
        complete: () => {
            console.log("Morphing complete.");
            if (infoEl) {
                infoEl.innerText = `Shape: "${text}"`;
                infoEl.style.textShadow = '0 0 5px rgba(0, 128, 255, 0.8)';
            }
            currentPositions.set(targetPositions[currentShapeIndex]);
            particlesGeometry.attributes.position.needsUpdate = true;
            particleEffectStrengths.fill(0.0);
            particlesGeometry.attributes.aEffectStrength.needsUpdate = true;
            sourcePositions.set(targetPositions[currentShapeIndex]);
            updateColors();
            isMorphing = false; controls.autoRotate = true;
        }
    });
}

function setupPostProcessing() {
    composer = new EffectComposer(renderer);
    composer.addPass(new RenderPass(scene, camera));
    bloomPass = new UnrealBloomPass(new THREE.Vector2(window.innerWidth, window.innerHeight), CONFIG.bloomStrength, CONFIG.bloomRadius, CONFIG.bloomThreshold);
    composer.addPass(bloomPass);
}

function createStarfield() {
    const starVertices = []; const starSizes = []; const starColors = [];
    const starGeometry = new THREE.BufferGeometry();
    for (let i = 0; i < CONFIG.starCount; i++) {
        tempVec.set(THREE.MathUtils.randFloatSpread(400), THREE.MathUtils.randFloatSpread(400), THREE.MathUtils.randFloatSpread(400));
        if (tempVec.length() < 100) tempVec.setLength(100 + Math.random() * 300);
        starVertices.push(tempVec.x, tempVec.y, tempVec.z);
        starSizes.push(Math.random() * 0.15 + 0.05);
        const color = new THREE.Color();
        if (Math.random() < 0.1) { color.setHSL(Math.random(), 0.7, 0.65); } else { color.setHSL(0.6, Math.random() * 0.1, 0.8 + Math.random() * 0.2); }
        starColors.push(color.r, color.g, color.b);
    }
    starGeometry.setAttribute('position', new THREE.Float32BufferAttribute(starVertices, 3));
    starGeometry.setAttribute('color', new THREE.Float32BufferAttribute(starColors, 3));
    starGeometry.setAttribute('size', new THREE.Float32BufferAttribute(starSizes, 1));
    const starMaterial = new THREE.ShaderMaterial({
        uniforms: { pointTexture: { value: createStarTexture() } },
        vertexShader: `
                      attribute float size; varying vec3 vColor; varying float vSize;
                      void main() {
                           vColor = color; vSize = size; vec4 mvPosition = modelViewMatrix * vec4(position, 1.0);
                           gl_PointSize = size * (400.0 / -mvPosition.z); gl_Position = projectionMatrix * mvPosition;
                      }`,
        fragmentShader: `
                      uniform sampler2D pointTexture; varying vec3 vColor; varying float vSize;
                      void main() {
                           float alpha = texture2D(pointTexture, gl_PointCoord).a; if (alpha < 0.1) discard;
                           gl_FragColor = vec4(vColor, alpha * 0.9);
                      }`,
        blending: THREE.AdditiveBlending, depthWrite: false, transparent: true, vertexColors: true
    });
    scene.add(new THREE.Points(starGeometry, starMaterial));
}

function createStarTexture() {
    const size = 64; const canvas = document.createElement('canvas');
    canvas.width = size; canvas.height = size; const context = canvas.getContext('2d');
    const gradient = context.createRadialGradient(size / 2, size / 2, 0, size / 2, size / 2, size / 2);
    gradient.addColorStop(0, 'rgba(255,255,255,1)'); gradient.addColorStop(0.2, 'rgba(255,255,255,0.8)');
    gradient.addColorStop(0.5, 'rgba(255,255,255,0.3)'); gradient.addColorStop(1, 'rgba(255,255,255,0)');
    context.fillStyle = gradient; context.fillRect(0, 0, size, size);
    return new THREE.CanvasTexture(canvas);
}

function setupParticleSystem() {
    targetPositions = SHAPES.map(shape => shape.generator(CONFIG.particleCount, CONFIG.shapeSize));
    particlesGeometry = new THREE.BufferGeometry();

    currentPositions = new Float32Array(targetPositions[0]);
    sourcePositions = new Float32Array(targetPositions[0]);
    swarmPositions = new Float32Array(CONFIG.particleCount * 3);
    particlesGeometry.setAttribute('position', new THREE.BufferAttribute(currentPositions, 3));

    particleSizes = new Float32Array(CONFIG.particleCount);
    particleOpacities = new Float32Array(CONFIG.particleCount);
    particleEffectStrengths = new Float32Array(CONFIG.particleCount);
    for (let i = 0; i < CONFIG.particleCount; i++) {
        particleSizes[i] = THREE.MathUtils.randFloat(CONFIG.particleSizeRange[0], CONFIG.particleSizeRange[1]);
        particleOpacities[i] = 1.0;
        particleEffectStrengths[i] = 0.0;
    }
    particlesGeometry.setAttribute('size', new THREE.BufferAttribute(particleSizes, 1));
    particlesGeometry.setAttribute('opacity', new THREE.BufferAttribute(particleOpacities, 1));
    particlesGeometry.setAttribute('aEffectStrength', new THREE.BufferAttribute(particleEffectStrengths, 1));

    const colors = new Float32Array(CONFIG.particleCount * 3);
    updateColorArray(colors, currentPositions);
    particlesGeometry.setAttribute('color', new THREE.BufferAttribute(colors, 3));

    particlesMaterial = new THREE.ShaderMaterial({
        uniforms: {
            pointTexture: { value: createStarTexture() }
        },
        vertexShader: `
                      attribute float size;
                      attribute float opacity;
                      attribute float aEffectStrength;
                      varying vec3 vColor;
                      varying float vOpacity;
                      varying float vEffectStrength;

                      void main() {
                           vColor = color;
                           vOpacity = opacity;
                           vEffectStrength = aEffectStrength;

                           vec4 mvPosition = modelViewMatrix * vec4(position, 1.0);

                           float sizeScale = 1.0 - vEffectStrength * ${CONFIG.morphSizeFactor.toFixed(2)};
                           gl_PointSize = size * sizeScale * (400.0 / -mvPosition.z);

                           gl_Position = projectionMatrix * mvPosition;
                      }
                 `,
        fragmentShader: `
                      uniform sampler2D pointTexture;
                      varying vec3 vColor;
                      varying float vOpacity;
                      varying float vEffectStrength;

                      void main() {
                           float alpha = texture2D(pointTexture, gl_PointCoord).a;
                           if (alpha < 0.05) discard;

                           vec3 finalColor = vColor * (1.0 + vEffectStrength * ${CONFIG.morphBrightnessFactor.toFixed(2)});

                           gl_FragColor = vec4(finalColor, alpha * vOpacity);
                      }
                 `,
        blending: THREE.AdditiveBlending,
        depthTest: true,
        depthWrite: false,
        transparent: true,
        vertexColors: true
    });

    particleSystem = new THREE.Points(particlesGeometry, particlesMaterial);
    scene.add(particleSystem);
}

function updateColorArray(colors, positionsArray) {
    const colorScheme = COLOR_SCHEMES[CONFIG.colorScheme];
    const center = new THREE.Vector3(0, 0, 0);
    const maxRadius = CONFIG.shapeSize * 1.1;
    for (let i = 0; i < CONFIG.particleCount; i++) {
        const i3 = i * 3;
        tempVec.fromArray(positionsArray, i3);
        const dist = tempVec.distanceTo(center);
        let hue;
        if (CONFIG.colorScheme === 'rainbow') {
            const normX = (tempVec.x / maxRadius + 1) / 2; const normY = (tempVec.y / maxRadius + 1) / 2; const normZ = (tempVec.z / maxRadius + 1) / 2;
            hue = (normX * 120 + normY * 120 + normZ * 120) % 360;
        } else {
            hue = THREE.MathUtils.mapLinear(dist, 0, maxRadius, colorScheme.startHue, colorScheme.endHue);
        }
        const noiseValue = (noise3D(tempVec.x * 0.2, tempVec.y * 0.2, tempVec.z * 0.2) + 1) * 0.5;
        const saturation = THREE.MathUtils.clamp(colorScheme.saturation * (0.9 + noiseValue * 0.2), 0, 1);
        const lightness = THREE.MathUtils.clamp(colorScheme.lightness * (0.85 + noiseValue * 0.3), 0.1, 0.9);
        const color = new THREE.Color().setHSL(hue / 360, saturation, lightness);
        color.toArray(colors, i3);
    }
}

function updateColors() {
    const colors = particlesGeometry.attributes.color.array;
    updateColorArray(colors, particlesGeometry.attributes.position.array);
    particlesGeometry.attributes.color.needsUpdate = true;
}

function updateTitle(index) {
    const titleEl = document.getElementById('hero-title');
    if (titleEl && TITLES[index]) {
        titleEl.classList.add('fade-out');
        setTimeout(() => {
            titleEl.innerText = TITLES[index];
            titleEl.classList.remove('fade-out');
        }, 500);
    }
}

function triggerMorph() {
    if (isMorphing) return;
    isMorphing = true; controls.autoRotate = false; console.log("Morphing triggered...");
    const infoEl = document.getElementById('info');
    if (infoEl) {
        infoEl.innerText = `Morphing...`;
        infoEl.style.textShadow = '0 0 8px rgba(255, 150, 50, 0.9)';
    }

    sourcePositions.set(currentPositions);

    let nextShapeIndex = (currentShapeIndex + 1);
    if (nextShapeIndex >= SHAPES.length) nextShapeIndex = 0;

    updateTitle(nextShapeIndex);

    const nextTargetPositions = targetPositions[nextShapeIndex];
    const centerOffsetAmount = CONFIG.shapeSize * CONFIG.swarmDistanceFactor;
    for (let i = 0; i < CONFIG.particleCount; i++) {
        const i3 = i * 3;
        sourceVec.fromArray(sourcePositions, i3); targetVec.fromArray(nextTargetPositions, i3);
        swarmVec.lerpVectors(sourceVec, targetVec, 0.5);
        const offsetDir = tempVec.set(noise3D(i * 0.05, 10, 10), noise3D(20, i * 0.05, 20), noise3D(30, 30, i * 0.05)).normalize();
        const distFactor = sourceVec.distanceTo(targetVec) * 0.1 + centerOffsetAmount;
        swarmVec.addScaledVector(offsetDir, distFactor * (0.5 + Math.random() * 0.8));
        swarmPositions[i3] = swarmVec.x; swarmPositions[i3 + 1] = swarmVec.y; swarmPositions[i3 + 2] = swarmVec.z;
    }
    currentShapeIndex = nextShapeIndex;
    morphState.progress = 0;
    if (morphTimeline) morphTimeline.pause();
    morphTimeline = anime({
        targets: morphState, progress: 1, duration: CONFIG.morphDuration, easing: 'cubicBezier(0.4, 0.0, 0.2, 1.0)',
        complete: () => {
            console.log("Morphing complete.");
            if (infoEl) {
                // Ensure SHAPES has the name, or fallback
                const shapeName = SHAPES[currentShapeIndex] ? SHAPES[currentShapeIndex].name : 'Custom';
                infoEl.innerText = `Shape: ${shapeName}`;
                infoEl.style.textShadow = '0 0 5px rgba(0, 128, 255, 0.8)';
            }
            currentPositions.set(targetPositions[currentShapeIndex]);
            particlesGeometry.attributes.position.needsUpdate = true;
            particleEffectStrengths.fill(0.0);
            particlesGeometry.attributes.aEffectStrength.needsUpdate = true;
            sourcePositions.set(targetPositions[currentShapeIndex]);
            updateColors();
            isMorphing = false; controls.autoRotate = true;
        }
    });
}

function animate() {
    requestAnimationFrame(animate);
    if (!isInitialized) return;
    const elapsedTime = clock.getElapsedTime();
    const deltaTime = clock.getDelta();
    controls.update();
    const positions = particlesGeometry.attributes.position.array;
    const effectStrengths = particlesGeometry.attributes.aEffectStrength.array;

    if (isMorphing) {
        updateMorphAnimation(positions, effectStrengths, elapsedTime, deltaTime);
    } else {
        updateIdleAnimation(positions, effectStrengths, elapsedTime, deltaTime);
    }
    particlesGeometry.attributes.position.needsUpdate = true;
    if (isMorphing || particlesGeometry.attributes.aEffectStrength.needsUpdate) {
        particlesGeometry.attributes.aEffectStrength.needsUpdate = true;
    }
    composer.render(deltaTime);
}

function updateMorphAnimation(positions, effectStrengths, elapsedTime, deltaTime) {
    const t = morphState.progress;
    // targetPositions is array of arrays.
    const targets = targetPositions[currentShapeIndex];
    const effectStrength = Math.sin(t * Math.PI);
    const currentSwirl = effectStrength * CONFIG.swirlFactor * deltaTime * 50;
    const currentNoise = effectStrength * CONFIG.noiseMaxStrength;

    for (let i = 0; i < CONFIG.particleCount; i++) {
        const i3 = i * 3;
        sourceVec.fromArray(sourcePositions, i3);
        swarmVec.fromArray(swarmPositions, i3);
        targetVec.fromArray(targets, i3);

        const t_inv = 1.0 - t; const t_inv_sq = t_inv * t_inv; const t_sq = t * t;
        bezPos.copy(sourceVec).multiplyScalar(t_inv_sq);
        bezPos.addScaledVector(swarmVec, 2.0 * t_inv * t);
        bezPos.addScaledVector(targetVec, t_sq);

        if (currentSwirl > 0.01) {
            tempVec.subVectors(bezPos, sourceVec);
            swirlAxis.set(noise3D(i * 0.02, elapsedTime * 0.1, 0), noise3D(0, i * 0.02, elapsedTime * 0.1 + 5), noise3D(elapsedTime * 0.1 + 10, 0, i * 0.02)).normalize();
            tempVec.applyAxisAngle(swirlAxis, currentSwirl * (0.5 + Math.random() * 0.5));
            bezPos.copy(sourceVec).add(tempVec);
        }

        if (currentNoise > 0.01) {
            const noiseTime = elapsedTime * CONFIG.noiseTimeScale;
            noiseOffset.set(noise4D(bezPos.x * CONFIG.noiseFrequency, bezPos.y * CONFIG.noiseFrequency, bezPos.z * CONFIG.noiseFrequency, noiseTime), noise4D(bezPos.x * CONFIG.noiseFrequency + 100, bezPos.y * CONFIG.noiseFrequency + 100, bezPos.z * CONFIG.noiseFrequency + 100, noiseTime), noise4D(bezPos.x * CONFIG.noiseFrequency + 200, bezPos.y * CONFIG.noiseFrequency + 200, bezPos.z * CONFIG.noiseFrequency + 200, noiseTime));
            bezPos.addScaledVector(noiseOffset, currentNoise);
        }

        positions[i3] = bezPos.x;
        positions[i3 + 1] = bezPos.y;
        positions[i3 + 2] = bezPos.z;

        effectStrengths[i] = effectStrength;
    }
    particlesGeometry.attributes.aEffectStrength.needsUpdate = true;
}

function updateIdleAnimation(positions, effectStrengths, elapsedTime, deltaTime) {
    const breathScale = 1.0 + Math.sin(elapsedTime * 0.5) * 0.015;
    const timeScaled = elapsedTime * CONFIG.idleFlowSpeed;
    const freq = 0.1;

    let needsEffectStrengthReset = false;

    for (let i = 0; i < CONFIG.particleCount; i++) {
        const i3 = i * 3;
        sourceVec.fromArray(sourcePositions, i3);
        tempVec.copy(sourceVec).multiplyScalar(breathScale);
        flowVec.set(noise4D(tempVec.x * freq, tempVec.y * freq, tempVec.z * freq, timeScaled), noise4D(tempVec.x * freq + 10, tempVec.y * freq + 10, tempVec.z * freq + 10, timeScaled), noise4D(tempVec.x * freq + 20, tempVec.y * freq + 20, tempVec.z * freq + 20, timeScaled));
        tempVec.addScaledVector(flowVec, CONFIG.idleFlowStrength);
        currentVec.fromArray(positions, i3);
        currentVec.lerp(tempVec, 0.05);
        positions[i3] = currentVec.x;
        positions[i3 + 1] = currentVec.y;
        positions[i3 + 2] = currentVec.z;

        if (effectStrengths[i] !== 0.0) {
            effectStrengths[i] = 0.0;
            needsEffectStrengthReset = true;
        }
    }
    if (needsEffectStrengthReset) {
        particlesGeometry.attributes.aEffectStrength.needsUpdate = true;
    }
}

function onCanvasClick(event) {
    if (event.target.closest('#sidebar')) { return; }
    triggerMorph();
}

function onWindowResize() {
    camera.aspect = window.innerWidth / window.innerHeight;
    camera.updateProjectionMatrix();
    renderer.setSize(window.innerWidth, window.innerHeight);
    composer.setSize(window.innerWidth, window.innerHeight);

    if (window.innerWidth <= 768) {
        camera.position.set(0, 8, 38);
        controls.target.set(0, -2.5, 0);
    } else {
        camera.position.set(0, 8, 28);
        controls.target.set(0, 0, 0);
    }
    controls.update();
}

init();
