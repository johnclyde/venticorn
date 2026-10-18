# Repository workflow

- Use reviewed pull requests and squash merges only. Keep main history linear. Never force push or bypass the repository rules.
- Finalize the PR title and description before merging. Pass that exact title as `commit_title` and that exact description as `commit_message`, with `merge_method=squash` and the reviewed head SHA. Do not rely on GitHub's editable merge-message defaults.
- After merging, read the resulting Git commit and verify its subject and body match the PR title and description, allowing only trailing newline normalization. Do not add a PR-number suffix to the commit title unless it is also in the PR title.
- Keep merged PR titles and descriptions aligned with their immutable commit messages. Do not edit one side alone or rewrite published history to make an editorial correction.
- Run validation locally. Do not add or enable GitHub Actions workflows.
- Never create, populate, or use GitHub Issues to record work for John Clyde. Use the project's established internal tracker and coordination records.
