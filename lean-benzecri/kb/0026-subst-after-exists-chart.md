# 0026 — Pitfall: `subst` the developing map after `exists_chart_of_injective`

*Found 2026-11-21 by T-bz-c2-developpement; recorded by the master session.*

After `obtain ⟨φ', hφ', hs, ht, he⟩ := exists_chart_of_injective hp hinj`, run `subst he`: the
developing map then becomes `⇑φ'` everywhere, and condition b of a pocket applies with `ψ := φ'`.
