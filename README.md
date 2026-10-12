# Bespoke — Thought-Experiment and Engineering Simulation Studio

A static, installable web application that turns a written idea or engineering problem into a
structured, computed and checked scientific investigation. Everything runs on the user's device.

## Modules

1. **Thought and imaginative experiments** — scientifically computable, logically analysable, and
   speculative or counterfactual, alone or mixed.
2. **Scientific, engineering and industrial simulation** — first-principles model generation
   (Option A) and candidate equation discovery (Option B).

Both include reverse engineering (from results back to inputs and equations), editable assumptions,
alternative worlds compared side by side, and export of reports, data, code and proof files.

## Running locally

    node tools/serve.mjs 8080      # then open http://localhost:8080/

No build step is needed to run. Before publishing, refresh the offline file list and the
self-hosting bundle:

    node tools/build.mjs

## Tests

    node tests/check-models.mjs    # contract, dimensional and benchmark checks for every model

## Hosting and resilience

The site is plain static files with relative paths: copy the folder to any web host. List other
hosts in `config.json` under `mirrors`; installed copies use them when the primary host is down.
Once opened, the application is stored on the device and works with no connection.

## Mathematical verification

Each equation is checked on-device for dimensional homogeneity, closure, and terms that can diverge
on the declared domain; singular terms receive a bounded, smooth replacement. A Lean 4 file is
generated for independent machine checking; the supporting library is in `lean/`.
Mathematical consistency is reported separately from physical credibility, which rests on
benchmarks, published measurements and the user's own data.
