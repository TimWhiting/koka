import { defineConfig } from 'vite';

export default defineConfig({
  base: './',
  build: {
    outDir: 'dist',
    sourcemap: true,
  },
  optimizeDeps: {
    include: ['monaco-editor'],
  },
  // In dev, use `web/public/` for static assets (all.js, precompiled/, lib/, manifests)
  // In production, these are assembled by the CI pipeline into the same dist/ folder
  publicDir: 'public',
});
