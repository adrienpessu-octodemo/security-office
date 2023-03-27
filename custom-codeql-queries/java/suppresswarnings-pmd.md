# Find SuppressWarnings("PMD") annotations
Avoid removing PMD warning. PMD is used to increase quality and security of the application code.


## Recommendation
First, instead of removing the warning, you should try to fix the issue if this is possible.

If this is a false positive or a bad configuration, you should ask the team responsible for the PMD configuration to fix it.

If you keep the suppresswarning note, you should add a comment explaining why the warning is suppressed.


## References
* [ PMD Website](https://pmd.github.io/)
* [ Security Office Repository](https://github.com/ghas-toulouse-demo/security-office)


