# Ferrum agent instructions

Ferrum aims to provide a native Rust verification backend for Prusti.

## Commit messages

Use Linux kernel-style commit messages:

- Start the subject with a subsystem prefix, followed by an imperative
  summary: `subsystem: Describe the change`.
- Keep subjects concise, preferably around 50 characters and no more than
  72 characters. Do not end the subject with a period.
- When a body is useful, separate it from the subject with a blank line.
  Explain the problem, why the change is needed, and relevant validation
  or tradeoffs. Wrap body text at approximately 72 characters.

## Working in logical chunks

- Keep each chunk focused, self-contained, and reviewable.
- Run the relevant checks before committing a chunk.
- Commit and push each completed logical chunk to the current branch's
  upstream as you go. Do not wait until the end of a large task to commit
  or push completed work.
- Keep unrelated changes in separate commits.
