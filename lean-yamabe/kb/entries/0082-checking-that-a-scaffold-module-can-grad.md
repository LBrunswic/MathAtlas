---
id: 0082
title: Checking that a scaffold module can graduate: compile a /tmp copy against import Yamabe
kind: pattern
created: 2026-11-23
---
Found by T-yamabe-thm-lower-bound. to check that a scaffold module can graduate without name clashes, compile a /tmp copy of it with its imports replaced by `import Yamabe` (the whole strict root), under -DwarningAsError=true. This takes seconds and writes nothing.
