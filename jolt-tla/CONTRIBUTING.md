# Contributing to Jolt TLA+

## How to Contribute

### Reporting Issues

Before submitting an issue:
1. Check existing issues for duplicates
2. Provide the TLA+ module name and line numbers
3. Include TLC output for bugs
4. Describe expected vs actual behavior

### Pull Requests

1. Fork the repository
2. Create a feature branch: `git checkout -b feature/your-feature`
3. Run TLC to verify your changes:
   ```bash
   java -jar tla2tools.jar -config Jolt.cfg JoltContinuations.tla -workers auto
   ```
4. All invariants must pass
5. Update CHANGELOG.md
6. Submit PR with clear description

### What We Accept

- Bug fixes in TLA+ specifications
- Additional invariants (with justification)
- Documentation improvements
- Conformance test vectors
- Prose specification clarifications

### Code Style

**TLA+ Files:**
- Follow existing formatting conventions
- Comment every operator with its purpose
- Reference prose spec sections (e.g., "See §11.10")
- Use consistent indentation (2 spaces)
- Keep lines under 80 characters where possible

**Markdown Files:**
- Use ATX-style headers (`#`, `##`, etc.)
- Include code blocks with language tags
- One sentence per line (for better diffs)

### Commit Messages

Use conventional commit format:

```
type: short description

[optional body]

[optional footer]
```

**Types:**
- `feat`: New feature or invariant
- `fix`: Bug fix
- `docs`: Documentation changes
- `refactor`: Code restructuring
- `test`: Test additions or changes

**Examples:**
```
feat: add chunk ordering invariant

Adds INV_ATK_NoChunkReorder to prevent attackers from
reordering chunks within a continuation.

Closes #42
```

```
fix: correct StateDigest field order

The config_tags were absorbed before step_counter,
but the spec requires step_counter first.

See §11.10.2 step 6.
```

```
docs: clarify SMT depth parameter
```

### Testing Changes

Before submitting:

1. **Syntax check:**
   ```bash
   java -cp tla2tools.jar tla2sany.SANY JoltContinuations.tla
   ```

2. **Model check:**
   ```bash
   java -jar tla2tools.jar -config Jolt.cfg JoltContinuations.tla -workers auto
   ```

3. **Expected output:**
   ```
   Model checking completed. No error has been found.
   ```

### Questions?

Open a discussion or issue. We're happy to help.

## License

By contributing, you agree that your contributions will be licensed under Apache 2.0.
