# ProofForge website

Product site for this repository. Lives in-tree so the compiler and the public
face stay in one place — not a second GitHub project.

```bash
cd website
npm install
npm run dev
```

GitHub Pages deploys from this folder via `.github/workflows/website.yml`.
After the first merge, set **Settings → Pages → Source** to GitHub Actions.

The public URL is `https://davirain-su.github.io/ProofForge/`.
