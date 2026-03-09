## Summary

- pin the verify workflow trigger contract in `check_verify_sync.py`
- require pushes to stay limited to `main` and require `workflow_dispatch` to remain enabled
- add regression coverage for trigger drift, including the live inline `branches: [main]` form

## Testing

- `python3 -m unittest scripts.test_check_verify_sync -v`
- `python3 scripts/check_verify_sync.py`
- `make check`
