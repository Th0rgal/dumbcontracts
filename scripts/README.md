# Scripts Quickstart

Use this file for day-to-day operation. Detailed script inventory lives in [REFERENCE.md](REFERENCE.md).

## High-signal commands

```bash
# Local CI-equivalent subset
make check

# Keep artifact/docs counters fresh
make refresh-status

# Run Python unit tests
make test-python

# Run Foundry differential tests
make test-foundry
```

## Sources of truth

- Verify workflow sync contract: `scripts/verify_sync_spec.json`
- Unified verify workflow validator: `scripts/check_verify_sync.py`
- Verification metrics: `artifacts/verification_status.json`
