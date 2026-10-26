# Branch recovery archive — 2026-10-26

This branch preserves the complete Git history of all 52 branch tips recorded in `branch-map.json` before consolidation to 10 branches. Every recorded tip is a parent of this archival commit (duplicate SHAs are listed once as parents), so historical source files and notes remain reachable.

This is a recovery container, not a mathematical integration or proof certification. Its tip contains only this README and the branch map. **Never merge this archive into main.** Main remains at `211b362c16ff6ef73e9a5f2f70c5cbb9a444cf80`; no Lean source, audit, build configuration, or proof target is changed by branch cleanup.

## Recovery

Find the desired original branch name and exact SHA in `branch-map.json`, then recreate that branch at its recorded commit using GitHub or Git. Example syntax:

```sh
git fetch origin archive/branch-consolidation-20261026
git branch <original-branch-name> <recorded-sha>
git push origin <original-branch-name>
```

The manifest's actions describe the cleanup plan; consult the live branch list for current state. The retained working references for Sections 3.8 and 5.2 already have their mathematical sources in main. The distinct unfinished sources remain on the Carleman repair, Lagrange continuation, and source assembly branches. The 45-item paper-gap tracker and named `leaned-paper` branch are also retained.
