import Causal.Morphism
import Causal.LinesCurves
import Causal.GlobalHyperbolicity

/-!
# Causal curves over an interval, extension, inextensibility

No paper label is certified by this file: "inextensible" is used about twenty times by the paper
and defined nowhere. The author ruled on its meaning (DEC-11, 2026-10-29) and confirmed this
file's definition as that ruling made precise, with one-sided notions as well (DEC-13,
2026-10-30). The file gives the definitions, sanity checks on the timelike line, and the two
facts the sketch of proof of `theo:geroch` (`ETT.tex:1268`) uses about inextensibility.

> Let $I$ be an interval of $\RR$. A causal curve $c:I\rightarrow M$ is a connected causal chain.
> (`def:causal_chronological_curve`, `ETT.tex:360`)

> If $I=]0,1]$ then $c$ is extensible by setting $c(0)=p$. Assume now $I=[0,1]$.
> Since $J^-(p)\neq \{p\}$ there exists $q'\in J^-(p)\setminus\{p\}$.
> By causal arc-connectedness we may extend $c$ by prepending a future causal curve from $q'$ to
> $p$, so $c$ is extensible. (`ETT.tex:1291`)

DEC-11: "inextensible" means **maximal under extension**: no causal curve strictly extends it.
DEC-13: a curve `c` over `I` is strictly extended by `c'` over `I'` if `c = c' ∘ φ` for a strictly
increasing `φ` onto a sub-interval of `I'` and `c'` takes a value `c` never takes; inextensible =
no strict extension. Past- and future-inextensibility are defined as well, one-sided.

## The definition

* A **future causal curve of `W` over the interval `I`** (`CausalCurveIn`) is a map `c : ℝ → M`
  which is a future causal curve of `W` (`Causal.Curves`) over every segment `[a, b] ⊆ I`; `I` is
  a non-empty interval. Only the values on `I` matter.
* `(I', c')` **strictly extends** `(I, c)` (`StrictlyExtends`) if `c'` is a future causal curve of
  `W` over the interval `I'`, there is a strictly increasing `φ : I → I'` whose image is a
  sub-interval of `I'` with `c' ∘ φ = c` on `I` (a reparametrisation of `c` sits inside `c'`),
  and **the image grows**: `c'` takes a value which `c` does not take.
* `c` is **inextensible** (`Inextensible`) if it is a causal curve over `I` and no curve strictly
  extends it.
* **One-sided** (DEC-13): an extension is **at the past end** (`StrictlyExtendsPast`) when the
  image of `φ` is a final segment of `I'` — all new parameters come before — and **at the future
  end** (`StrictlyExtendsFuture`) when it is an initial segment. `PastInextensible`,
  `FutureInextensible`: no strict extension at that end. A strict extension of a curve over a
  non-empty interval adds its new value at one of the two ends, so inextensible is past- and
  future-inextensible (`inextensible_iff`), and time reversal exchanges the two
  (`dual_pastInextensible_iff`, `dual_futureInextensible_iff`).

## The two traps, and how they are handled

1. **"Extends" cannot mean "larger domain, same values"**, because a causal curve need not be
   injective and a constant map is a causal curve (DEC-6): every curve over `[a, b]` extends by a
   constant piece to `[a, b + 1]` (`exists_naive_extension`), so nothing would be inextensible,
   and every time function would be a Cauchy time function. Asking that **the image grow**
   excludes that. Conversely, with domain inclusion and no reparametrisation, every curve over
   `ℝ` would be inextensible (no interval strictly contains `ℝ`), a constant curve over `ℝ`
   included, and no Cauchy time function would exist. Allowing the reparametrisation `φ` excludes
   that. Sanity, on the timelike line: `id` over `ℝ` is inextensible
   (`timelikeLine_inextensible_id`), `id` over `[0, 1]` is not
   (`timelikeLine_not_inextensible_Icc`), and `t ↦ min t 0` over `ℝ` is not
   (`timelikeLine_not_inextensible_min`): its constant tail is squeezed by `φ` into `[0, 1[`, and
   the new curve goes on rising after it, which only the reparametrisation clause allows.
2. The **image of `φ` is asked to be an interval**: the old curve is a sub-arc of the new one, and
   the extension happens at the ends only. Without it a curve could be "extended" by inserting a
   causal loop at an interior point, which only a non-causal spacetime allows.

## The two facts of the proof sketch

* **Prepending at a closed end** (`extensible_of_isLeast`, `ETT.tex:1292–1294`): a curve over an
  interval with a least point `a`, in a causally arc-connected **causal** spacetime, with
  `J^-_W(c a) ≠ {c a}`, is extensible. Causality is used to know that the new point `q'` is not
  already on the curve. The dual, appending at a greatest point: `extensible_of_isGreatest`.
* **A limit at an open end** (`ETT.tex:1291`). *As written this is false* in two ways, and the
  file proves the form the sketch can use. (a) Adjoining the limit point `p` keeps a causal curve
  only if `p` is causally related to the curve inside small open sets; the file proves it
  (`causalCurveIn_insert`) when the causal pasts `J^-(x)` are closed, `M` is strongly causal
  (DEC-7) and causally arc-connected — all available in the sketch, from global hyperbolicity.
  (b) Adjoining `p` need not make the image grow: if `c` is constant near the end, `p` is already
  on the curve. The sketch's next step (prepending, using `J^-(p) ≠ {p}`) repairs both cases:
  `extensible_of_tendsto` is the fact as used, adjoin then prepend.

## SCOPE (disclosed)

* Curves are **future** causal curves; a past causal curve is a future causal curve of `C.dual`,
  run backwards (`CausalCurveIn.reverse`). The past- and future-inextensibility of
  `ETT.tex:1295–1296` are `PastInextensible`, `FutureInextensible` (DEC-13); the constructions of
  the sketch are given in their one-sided form too (`pastExtensible_of_isLeast`,
  `pastExtensible_of_tendsto`, `PastExtensible.of_comp`).
* Extension is defined for causal curves only; chronal curves are not treated.
* `StrictlyExtends` does not ask `c` itself to be a curve; `Inextensible` does.
* **`φ` is automatically a homeomorphism onto its image**: a strictly increasing map from an
  interval onto an interval is an order isomorphism between them, hence continuous with
  continuous inverse for the order (= subspace) topologies. It is not asked to be continuous.
* **"The image grows" is not parametrised maximality** in a non-causal spacetime. A curve whose
  image is already all of `M` (a surjective curve), or a closed causal loop run forever, admits no
  extension whose image grows, so it is inextensible here although a longer parametrisation of it
  exists. In a causal spacetime the two notions are meant to agree (an extension that adds no
  point can only repeat endpoints); this is not proved.
* The definition of "extension" (image grows, reparametrisation allowed, sub-arc) is this file's
  formalization of DEC-11; the author confirmed it (DEC-13).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter

universe u

variable {M : Type u} [TopologicalSpace M]

/-! ### Three general facts about curves over a segment -/

namespace CurveOn

variable {r : Opens M → M → M → Prop} {W : Opens M} {c d : ℝ → M} {a b : ℝ}

/-- A curve depends only on its values on the segment. -/
theorem congr (hc : CurveOn r W c a b) (h : EqOn c d (Icc a b)) : CurveOn r W d a b where
  mem t ht := by rw [← h ht]; exact hc.mem t ht
  rel t ht N hN htN := by
    obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel t ht N hN (by rw [h ht]; exact htN)
    exact ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => by
      rw [← h hs, ← h hs']; exact hrel s hs s' hs' h1 h2 h3⟩

/-- Over an empty segment every map is a curve. -/
theorem of_lt (hab : b < a) : CurveOn r W c a b where
  mem _ ht := absurd (ht.1.trans ht.2) (not_le.2 hab)
  rel _ ht := absurd (ht.1.trans ht.2) (not_le.2 hab)

/-- Reparametrisation by a continuous strictly increasing map. -/
theorem comp_strictMonoOn {ψ : ℝ → ℝ} {a' b' : ℝ} (hc : CurveOn r W c (ψ a') (ψ b'))
    (hψ : StrictMonoOn ψ (Icc a' b')) (hψc : ContinuousOn ψ (Icc a' b')) :
    CurveOn r W (c ∘ ψ) a' b' := by
  have hmem : ∀ s ∈ Icc a' b', ψ s ∈ Icc (ψ a') (ψ b') := fun s hs =>
    ⟨hψ.monotoneOn ⟨le_rfl, hs.1.trans hs.2⟩ hs hs.1,
      hψ.monotoneOn hs ⟨hs.1.trans hs.2, le_rfl⟩ hs.2⟩
  refine ⟨fun t ht => hc.mem (ψ t) (hmem t ht), fun t ht N hN htN => ?_⟩
  obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel (ψ t) (hmem t ht) N hN htN
  have hev : ψ ⁻¹' Ioo l u ∈ 𝓝[Icc a' b'] t := hψc t ht (Ioo_mem_nhds hl hu)
  obtain ⟨O, hO, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hev
  obtain ⟨l', u', ⟨hl', hu'⟩, hlu'⟩ := mem_nhds_iff_exists_Ioo_subset.1 hO
  refine ⟨l', u', hl', hu', fun s hs s' hs' h1 h2 h3 => ?_⟩
  have hsI : ψ s ∈ Ioo l u := hsub ⟨hlu' ⟨h1, h2.trans h3⟩, hs⟩
  have hs'I : ψ s' ∈ Ioo l u := hsub ⟨hlu' ⟨h1.trans h2, h3⟩, hs'⟩
  exact hrel (ψ s) (hmem s hs) (ψ s') (hmem s' hs') hsI.1 (hψ hs hs' h2) hs'I.2

/-- Running a curve backwards gives a curve for the reversed relations. -/
theorem neg (hc : CurveOn r W c (-b) (-a)) :
    CurveOn (fun N x y => r N y x) W (fun t => c (-t)) a b where
  mem t ht := hc.mem (-t) ⟨neg_le_neg ht.2, neg_le_neg ht.1⟩
  rel t ht N hN htN := by
    obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel (-t) ⟨neg_le_neg ht.2, neg_le_neg ht.1⟩ N hN htN
    exact ⟨-u, -l, by linarith, by linarith, fun s hs s' hs' h1 h2 h3 =>
      hrel (-s') ⟨neg_le_neg hs'.2, neg_le_neg hs'.1⟩ (-s) ⟨neg_le_neg hs.2, neg_le_neg hs.1⟩
        (by linarith) (by linarith) (by linarith)⟩

end CurveOn

namespace Causality

variable (C : Causality M)

/-- A **future causal curve of the open set `W` over the interval `I`**: `I` is a non-empty
interval, and `c` is a future causal curve of `W` over every segment of `I`. -/
structure CausalCurveIn (W : Opens M) (I : Set ℝ) (c : ℝ → M) : Prop where
  nonempty : I.Nonempty
  ordConnected : I.OrdConnected
  curve : ∀ a ∈ I, ∀ b ∈ I, C.CausalCurveOn W c a b

/-- `(I', c')` **strictly extends** `(I, c)`: `c'` is a future causal curve of `W` over the
interval `I'`, a reparametrisation of `c` is a sub-arc of `c'`, and the image grows. -/
structure StrictlyExtends (W : Opens M) (I : Set ℝ) (c : ℝ → M) (I' : Set ℝ) (c' : ℝ → M) :
    Prop where
  curve : C.CausalCurveIn W I' c'
  reparam : ∃ φ : ℝ → ℝ, StrictMonoOn φ I ∧ MapsTo φ I I' ∧ (φ '' I).OrdConnected ∧
    ∀ t ∈ I, c' (φ t) = c t
  grows : ∃ t' ∈ I', ∀ t ∈ I, c' t' ≠ c t

/-- `c` over `I` is **extensible** in `W`: some causal curve of `W` strictly extends it. -/
def Extensible (W : Opens M) (I : Set ℝ) (c : ℝ → M) : Prop :=
  ∃ I' c', C.StrictlyExtends W I c I' c'

/-- DEC-11: `c` is an **inextensible** causal curve of `W` over `I`: a causal curve which no
causal curve strictly extends. -/
def Inextensible (W : Opens M) (I : Set ℝ) (c : ℝ → M) : Prop :=
  C.CausalCurveIn W I c ∧ ¬ C.Extensible W I c

variable {C} {W : Opens M} {I J I' : Set ℝ} {c c' d : ℝ → M} {a b : ℝ}

/-! ### Curves over an interval -/

namespace CausalCurveIn

/-- Along a curve over `I`, the causal relation of `W` holds in the order of the parameters. -/
theorem le_of_le (hc : C.CausalCurveIn W I c) {s s' : ℝ} (hs : s ∈ I) (hs' : s' ∈ I)
    (h : s ≤ s') : C.le W (c s) (c s') :=
  (hc.curve s hs s' hs').le_of_le le_rfl h le_rfl

theorem mem (hc : C.CausalCurveIn W I c) {s : ℝ} (hs : s ∈ I) : c s ∈ W :=
  (hc.curve s hs s hs).mem s ⟨le_rfl, le_rfl⟩

/-- Reparametrisation by a continuous strictly increasing map. -/
theorem comp (hc : C.CausalCurveIn W I c) {ψ : ℝ → ℝ} (hJ : J.Nonempty) (hJc : J.OrdConnected)
    (hψ : StrictMonoOn ψ J) (hψc : ContinuousOn ψ J) (hmaps : MapsTo ψ J I) :
    C.CausalCurveIn W J (c ∘ ψ) where
  nonempty := hJ
  ordConnected := hJc
  curve a ha b hb := by
    rcases le_or_gt a b with hab | hab
    · have hsub : Icc a b ⊆ J := hJc.out ha hb
      exact CurveOn.comp_strictMonoOn (hc.curve _ (hmaps ha) _ (hmaps hb)) (hψ.mono hsub)
        (hψc.mono hsub)
    · exact CurveOn.of_lt hab

/-- Time reversal: a future causal curve of `C`, run backwards, is a future causal curve of
`C.dual`. -/
theorem reverse (hc : C.CausalCurveIn W I c) :
    C.dual.CausalCurveIn W (-I) (fun t => c (-t)) where
  nonempty := by
    obtain ⟨t, ht⟩ := hc.nonempty
    exact ⟨-t, by simpa using ht⟩
  ordConnected := ⟨fun x hx y hy z hz =>
    hc.ordConnected.out hy hx ⟨neg_le_neg hz.2, neg_le_neg hz.1⟩⟩
  curve a ha b hb := CurveOn.neg (hc.curve (-b) hb (-a) ha)

/-- A curve over `ℝ` is continuous. -/
theorem continuous (hc : C.CausalCurveIn ⊤ univ c) : Continuous c :=
  continuous_of_curveOn C.isRelFamily_le fun a b => hc.curve a trivial b trivial

end CausalCurveIn

/-! ### Transport of extensions -/

/-- Extensibility transported along a strictly increasing reparametrisation: if `d ∘ ψ = c` on `I`
and `ψ` maps `I` onto `J`, an extension of `d` over `J` is an extension of `c` over `I`. -/
theorem Extensible.of_comp {ψ : ℝ → ℝ} (hd : C.Extensible W J d) (hψ : StrictMonoOn ψ I)
    (hmaps : MapsTo ψ I J) (hsurj : SurjOn ψ I J) (heq : ∀ t ∈ I, d (ψ t) = c t) :
    C.Extensible W I c := by
  obtain ⟨I', c', hcurve, ⟨φ, hφ, hφmaps, hφoc, hφeq⟩, ⟨t', ht', hgrow⟩⟩ := hd
  refine ⟨I', c', hcurve, ⟨φ ∘ ψ, ?_, ?_, ?_, ?_⟩, ⟨t', ht', ?_⟩⟩
  · intro s hs s' hs' h
    exact hφ (hmaps hs) (hmaps hs') (hψ hs hs' h)
  · intro s hs
    exact hφmaps (hmaps hs)
  · rw [image_comp, hsurj.image_eq_of_mapsTo hmaps]
    exact hφoc
  · intro t ht
    simp only [Function.comp]
    rw [hφeq _ (hmaps ht), heq t ht]
  · intro t ht h
    exact hgrow (ψ t) (hmaps ht) (by rw [heq t ht]; exact h)

/-- Extensibility for the reversed causality, of the reversed curve, is extensibility. -/
theorem Extensible.of_dual_reverse (h : C.dual.Extensible W (-I) (fun t => c (-t))) :
    C.Extensible W I c := by
  obtain ⟨I', c', hcurve, ⟨φ, hφ, hφmaps, hφoc, hφeq⟩, ⟨t', ht', hgrow⟩⟩ := h
  have hneg : ∀ {t : ℝ}, t ∈ I → -t ∈ -I := fun ht => by simpa using ht
  refine ⟨-I', fun t => c' (-t), hcurve.reverse, ⟨fun t => -φ (-t), ?_, ?_, ?_, ?_⟩,
    ⟨-t', by simpa using ht', ?_⟩⟩
  · intro s hs s' hs' h
    exact neg_lt_neg (hφ (hneg hs') (hneg hs) (neg_lt_neg h))
  · intro s hs
    show -(-φ (-s)) ∈ I'
    rw [neg_neg]
    exact hφmaps (hneg hs)
  · refine ⟨fun x hx y hy z hz => ?_⟩
    obtain ⟨s₁, hs₁, rfl⟩ := hx
    obtain ⟨s₂, hs₂, rfl⟩ := hy
    have hz' : -z ∈ Icc (φ (-s₂)) (φ (-s₁)) :=
      ⟨by linarith [hz.2], by linarith [hz.1]⟩
    obtain ⟨w, hw, hwz⟩ := hφoc.out (mem_image_of_mem φ (hneg hs₂))
      (mem_image_of_mem φ (hneg hs₁)) hz'
    refine ⟨-w, hw, ?_⟩
    show -φ (-(-w)) = z
    rw [neg_neg, hwz, neg_neg]
  · intro t ht
    show c' (-(-φ (-t))) = c t
    rw [neg_neg, hφeq (-t) (hneg ht), neg_neg]
  · intro t ht
    have := hgrow (-t) (hneg ht)
    simpa using this

/-- An inextensible curve, run backwards, is inextensible for the reversed causality. -/
theorem Inextensible.dual_reverse (h : C.Inextensible W I c) :
    C.dual.Inextensible W (-I) (fun t => c (-t)) :=
  ⟨h.1.reverse, fun he => h.2 he.of_dual_reverse⟩

/-! ### One-sided inextensibility (DEC-13) -/

variable (C) in
/-- `c'` over `I'` strictly extends `c` over `I` **at the past end** (DEC-13): a strict extension
whose new parameters all lie before the image of `φ`, which is a final segment of `I'`. -/
def StrictlyExtendsPast (W : Opens M) (I : Set ℝ) (c : ℝ → M) (I' : Set ℝ) (c' : ℝ → M) :
    Prop :=
  C.CausalCurveIn W I' c' ∧
    (∃ φ : ℝ → ℝ, StrictMonoOn φ I ∧ MapsTo φ I I' ∧ (φ '' I).OrdConnected ∧
      (∀ t ∈ I, c' (φ t) = c t) ∧ ∀ t ∈ I, ∀ t' ∈ I', φ t ≤ t' → t' ∈ φ '' I) ∧
    ∃ t' ∈ I', ∀ t ∈ I, c' t' ≠ c t

variable (C) in
/-- `c'` over `I'` strictly extends `c` over `I` **at the future end** (DEC-13): the image of `φ`
is an initial segment of `I'`. -/
def StrictlyExtendsFuture (W : Opens M) (I : Set ℝ) (c : ℝ → M) (I' : Set ℝ) (c' : ℝ → M) :
    Prop :=
  C.CausalCurveIn W I' c' ∧
    (∃ φ : ℝ → ℝ, StrictMonoOn φ I ∧ MapsTo φ I I' ∧ (φ '' I).OrdConnected ∧
      (∀ t ∈ I, c' (φ t) = c t) ∧ ∀ t ∈ I, ∀ t' ∈ I', t' ≤ φ t → t' ∈ φ '' I) ∧
    ∃ t' ∈ I', ∀ t ∈ I, c' t' ≠ c t

variable (C) in
/-- `c` is **extensible at the past end**. -/
def PastExtensible (W : Opens M) (I : Set ℝ) (c : ℝ → M) : Prop :=
  ∃ I' c', C.StrictlyExtendsPast W I c I' c'

variable (C) in
/-- `c` is **extensible at the future end**. -/
def FutureExtensible (W : Opens M) (I : Set ℝ) (c : ℝ → M) : Prop :=
  ∃ I' c', C.StrictlyExtendsFuture W I c I' c'

variable (C) in
/-- DEC-13: `c` is **past-inextensible**: a causal curve with no strict extension at the past
end. -/
def PastInextensible (W : Opens M) (I : Set ℝ) (c : ℝ → M) : Prop :=
  C.CausalCurveIn W I c ∧ ¬ C.PastExtensible W I c

variable (C) in
/-- DEC-13: `c` is **future-inextensible**. -/
def FutureInextensible (W : Opens M) (I : Set ℝ) (c : ℝ → M) : Prop :=
  C.CausalCurveIn W I c ∧ ¬ C.FutureExtensible W I c

theorem PastExtensible.extensible (h : C.PastExtensible W I c) : C.Extensible W I c := by
  obtain ⟨I', c', hcurve, ⟨φ, h1, h2, h3, h4, -⟩, hgrow⟩ := h
  exact ⟨I', c', hcurve, ⟨φ, h1, h2, h3, h4⟩, hgrow⟩

theorem FutureExtensible.extensible (h : C.FutureExtensible W I c) : C.Extensible W I c := by
  obtain ⟨I', c', hcurve, ⟨φ, h1, h2, h3, h4, -⟩, hgrow⟩ := h
  exact ⟨I', c', hcurve, ⟨φ, h1, h2, h3, h4⟩, hgrow⟩

/-- A strict extension of a curve over a non-empty interval adds a value at one of the two ends:
extensible is extensible at the past end or at the future end. -/
theorem extensible_iff (hI : I.Nonempty) :
    C.Extensible W I c ↔ C.PastExtensible W I c ∨ C.FutureExtensible W I c := by
  refine ⟨fun h => ?_, fun h => h.elim PastExtensible.extensible FutureExtensible.extensible⟩
  obtain ⟨I', c', hcurve, ⟨φ, hφ, hmaps, hoc, heq⟩, ⟨t', ht', hgrow⟩⟩ := h
  obtain ⟨t₀, ht₀⟩ := hI
  have hnot : t' ∉ φ '' I := by
    rintro ⟨t, ht, rfl⟩
    exact hgrow t ht (heq t ht)
  by_cases hbelow : ∀ t ∈ I, t' < φ t
  · left
    refine ⟨I' ∩ {u | ∃ t ∈ I, u ≤ φ t}, c', ⟨⟨t', ht', t₀, ht₀, (hbelow t₀ ht₀).le⟩,
      ⟨fun x hx y hy z hz => ?_⟩, fun a ha b hb => hcurve.curve a ha.1 b hb.1⟩,
      ⟨φ, hφ, fun t ht => ⟨hmaps ht, t, ht, le_rfl⟩, hoc, heq, ?_⟩,
      ⟨t', ⟨ht', t₀, ht₀, (hbelow t₀ ht₀).le⟩, hgrow⟩⟩
    · obtain ⟨t, ht, hyt⟩ := hy.2
      exact ⟨hcurve.ordConnected.out hx.1 hy.1 hz, t, ht, hz.2.trans hyt⟩
    · rintro t ht u ⟨-, t₂, ht₂, hut₂⟩ htu
      exact hoc.out (mem_image_of_mem φ ht) (mem_image_of_mem φ ht₂) ⟨htu, hut₂⟩
  · right
    obtain ⟨t₁, ht₁, h₁⟩ : ∃ t ∈ I, φ t ≤ t' := by
      by_contra h'
      exact hbelow fun t ht => lt_of_not_ge fun h => h' ⟨t, ht, h⟩
    have habove : ∀ t ∈ I, φ t < t' := fun t ht => lt_of_not_ge fun h =>
      hnot (hoc.out (mem_image_of_mem φ ht₁) (mem_image_of_mem φ ht) ⟨h₁, h⟩)
    refine ⟨I' ∩ {u | ∃ t ∈ I, φ t ≤ u}, c', ⟨⟨t', ht', t₁, ht₁, h₁⟩,
      ⟨fun x hx y hy z hz => ?_⟩, fun a ha b hb => hcurve.curve a ha.1 b hb.1⟩,
      ⟨φ, hφ, fun t ht => ⟨hmaps ht, t, ht, le_rfl⟩, hoc, heq, ?_⟩,
      ⟨t', ⟨ht', t₁, ht₁, h₁⟩, hgrow⟩⟩
    · obtain ⟨t, ht, hxt⟩ := hx.2
      exact ⟨hcurve.ordConnected.out hx.1 hy.1 hz, t, ht, hxt.trans hz.1⟩
    · rintro t ht u ⟨-, t₂, ht₂, ht₂u⟩ hut
      exact hoc.out (mem_image_of_mem φ ht₂) (mem_image_of_mem φ ht) ⟨ht₂u, hut⟩

/-- **DEC-13: inextensible is past- and future-inextensible.** -/
theorem inextensible_iff :
    C.Inextensible W I c ↔ C.PastInextensible W I c ∧ C.FutureInextensible W I c :=
  ⟨fun h => ⟨⟨h.1, fun hp => h.2 hp.extensible⟩, ⟨h.1, fun hf => h.2 hf.extensible⟩⟩,
    fun h => ⟨h.1.1, fun he => ((extensible_iff h.1.1.nonempty).1 he).elim h.1.2 h.2.2⟩⟩

/-- Time reversal exchanges the ends: an extension at the past end for the reversed causality,
of the reversed curve, is an extension at the future end. -/
theorem FutureExtensible.of_dual_reverse
    (h : C.dual.PastExtensible W (-I) (fun t => c (-t))) : C.FutureExtensible W I c := by
  obtain ⟨I', c', hcurve, ⟨φ, hφ, hφmaps, hφoc, hφeq, hφend⟩, ⟨t', ht', hgrow⟩⟩ := h
  have hneg : ∀ {t : ℝ}, t ∈ I → -t ∈ -I := fun ht => by simpa using ht
  refine ⟨-I', fun t => c' (-t), hcurve.reverse, ⟨fun t => -φ (-t), ?_, ?_, ?_, ?_, ?_⟩,
    ⟨-t', by simpa using ht', ?_⟩⟩
  · intro s hs s' hs' h
    exact neg_lt_neg (hφ (hneg hs') (hneg hs) (neg_lt_neg h))
  · intro s hs
    show -(-φ (-s)) ∈ I'
    rw [neg_neg]
    exact hφmaps (hneg hs)
  · refine ⟨fun x hx y hy z hz => ?_⟩
    obtain ⟨s₁, hs₁, rfl⟩ := hx
    obtain ⟨s₂, hs₂, rfl⟩ := hy
    have hz' : -z ∈ Icc (φ (-s₂)) (φ (-s₁)) :=
      ⟨by linarith [hz.2], by linarith [hz.1]⟩
    obtain ⟨w, hw, hwz⟩ := hφoc.out (mem_image_of_mem φ (hneg hs₂))
      (mem_image_of_mem φ (hneg hs₁)) hz'
    refine ⟨-w, hw, ?_⟩
    show -φ (-(-w)) = z
    rw [neg_neg, hwz, neg_neg]
  · intro t ht
    show c' (-(-φ (-t))) = c t
    rw [neg_neg, hφeq (-t) (hneg ht)]; simp only [neg_neg]
  · intro t ht v hv hvt
    obtain ⟨w, hw, hwv⟩ := hφend (-t) (hneg ht) (-v) hv (by linarith)
    refine ⟨-w, hw, ?_⟩
    show -φ (-(-w)) = v
    rw [neg_neg, hwv, neg_neg]
  · intro t ht
    have := hgrow (-t) (hneg ht)
    simpa using this

/-- Time reversal exchanges the ends, the other way. -/
theorem PastExtensible.of_dual_reverse
    (h : C.dual.FutureExtensible W (-I) (fun t => c (-t))) : C.PastExtensible W I c := by
  obtain ⟨I', c', hcurve, ⟨φ, hφ, hφmaps, hφoc, hφeq, hφend⟩, ⟨t', ht', hgrow⟩⟩ := h
  have hneg : ∀ {t : ℝ}, t ∈ I → -t ∈ -I := fun ht => by simpa using ht
  refine ⟨-I', fun t => c' (-t), hcurve.reverse, ⟨fun t => -φ (-t), ?_, ?_, ?_, ?_, ?_⟩,
    ⟨-t', by simpa using ht', ?_⟩⟩
  · intro s hs s' hs' h
    exact neg_lt_neg (hφ (hneg hs') (hneg hs) (neg_lt_neg h))
  · intro s hs
    show -(-φ (-s)) ∈ I'
    rw [neg_neg]
    exact hφmaps (hneg hs)
  · refine ⟨fun x hx y hy z hz => ?_⟩
    obtain ⟨s₁, hs₁, rfl⟩ := hx
    obtain ⟨s₂, hs₂, rfl⟩ := hy
    have hz' : -z ∈ Icc (φ (-s₂)) (φ (-s₁)) :=
      ⟨by linarith [hz.2], by linarith [hz.1]⟩
    obtain ⟨w, hw, hwz⟩ := hφoc.out (mem_image_of_mem φ (hneg hs₂))
      (mem_image_of_mem φ (hneg hs₁)) hz'
    refine ⟨-w, hw, ?_⟩
    show -φ (-(-w)) = z
    rw [neg_neg, hwz, neg_neg]
  · intro t ht
    show c' (-(-φ (-t))) = c t
    rw [neg_neg, hφeq (-t) (hneg ht)]; simp only [neg_neg]
  · intro t ht v hv hvt
    obtain ⟨w, hw, hwv⟩ := hφend (-t) (hneg ht) (-v) hv (by linarith)
    refine ⟨-w, hw, ?_⟩
    show -φ (-(-w)) = v
    rw [neg_neg, hwv, neg_neg]
  · intro t ht
    have := hgrow (-t) (hneg ht)
    simpa using this

/-- **Duality of the one-sided notions**: a curve is future-inextensible iff, run backwards, it is
past-inextensible for the reversed causality. -/
theorem dual_pastInextensible_iff :
    C.dual.PastInextensible W (-I) (fun t => c (-t)) ↔ C.FutureInextensible W I c := by
  constructor
  · intro h
    refine ⟨by simpa using h.1.reverse, fun hf => h.2 ?_⟩
    exact PastExtensible.of_dual_reverse (C := C.dual) (I := -I) (c := fun t => c (-t))
      (by simpa using hf)
  · intro h
    exact ⟨h.1.reverse, fun hp => h.2 (FutureExtensible.of_dual_reverse hp)⟩

/-- The other duality: past-inextensible iff, run backwards, future-inextensible for the
reversed causality. -/
theorem dual_futureInextensible_iff :
    C.dual.FutureInextensible W (-I) (fun t => c (-t)) ↔ C.PastInextensible W I c := by
  constructor
  · intro h
    refine ⟨by simpa using h.1.reverse, fun hp => h.2 ?_⟩
    exact FutureExtensible.of_dual_reverse (C := C.dual) (I := -I) (c := fun t => c (-t))
      (by simpa using hp)
  · intro h
    exact ⟨h.1.reverse, fun hf => h.2 (PastExtensible.of_dual_reverse hf)⟩

/-- Extensibility at the past end transported along a strictly increasing reparametrisation. -/
theorem PastExtensible.of_comp {ψ : ℝ → ℝ} (hd : C.PastExtensible W J d) (hψ : StrictMonoOn ψ I)
    (hmaps : MapsTo ψ I J) (hsurj : SurjOn ψ I J) (heq : ∀ t ∈ I, d (ψ t) = c t) :
    C.PastExtensible W I c := by
  obtain ⟨I', c', hcurve, ⟨φ, hφ, hφmaps, hφoc, hφeq, hφend⟩, ⟨t', ht', hgrow⟩⟩ := hd
  have himg : (φ ∘ ψ) '' I = φ '' J := by rw [image_comp, hsurj.image_eq_of_mapsTo hmaps]
  refine ⟨I', c', hcurve, ⟨φ ∘ ψ, ?_, ?_, ?_, ?_, ?_⟩, ⟨t', ht', ?_⟩⟩
  · intro s hs s' hs' h
    exact hφ (hmaps hs) (hmaps hs') (hψ hs hs' h)
  · intro s hs
    exact hφmaps (hmaps hs)
  · rw [himg]; exact hφoc
  · intro t ht
    simp only [Function.comp]
    rw [hφeq _ (hmaps ht), heq t ht]
  · intro t ht u hu htu
    rw [himg]
    exact hφend (ψ t) (hmaps ht) u hu htu
  · intro t ht h
    exact hgrow (ψ t) (hmaps ht) (by rw [heq t ht]; exact h)

/-! ### Trap 1: the naive definition is vacuous -/

/-- **Trap 1.** Every causal curve over a segment `[a, b]` "extends", in the naive sense of a
larger domain and the same values, to `[a, b + 1]`, by a constant piece: the image does not grow.
This is why `StrictlyExtends` asks the image to grow. -/
theorem exists_naive_extension (hc : C.CausalCurveOn W c a b) (hab : a ≤ b) :
    ∃ c' : ℝ → M, C.CausalCurveOn W c' a (b + 1) ∧ EqOn c' c (Icc a b) ∧
      c' '' Icc a (b + 1) = c '' Icc a b := by
  have hconst : C.CausalCurveOn W (fun _ => c b) b (b + 1) :=
    causalCurveOn_const (hc.mem b ⟨hab, le_rfl⟩)
  refine ⟨fun t => if t ≤ b then c t else c b,
    CurveOn.concat C.isRelFamily_le hc hconst hab (by linarith) rfl, ?_, ?_⟩
  · intro t ht
    simp [ht.2]
  · ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      by_cases h : t ≤ b
      · exact ⟨t, ⟨ht.1, h⟩, by simp [h]⟩
      · exact ⟨b, ⟨hab, le_rfl⟩, by simp [h]⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ⟨ht.1, ht.2.trans (by linarith)⟩, by simp [ht.2]⟩

end Causality

/-! ### Sanity on the timelike line -/

/-- The identity is a causal curve of the timelike line over every segment. -/
theorem timelikeLine_causalCurveOn_id (a b : ℝ) : timelikeLine.CausalCurveOn ⊤ id a b where
  mem _ _ := trivial
  rel t _ N _ htN := by
    obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 (N.isOpen.mem_nhds htN)
    exact ⟨l, u, hl, hu, fun s _ s' _ h1 h2 h3 =>
      timelikeLine_le.2 ⟨h2.le, fun z hz => hsub ⟨h1.trans_le hz.1, hz.2.trans_lt h3⟩⟩⟩

theorem timelikeLine_causalCurveIn_id {I : Set ℝ} (hI : I.Nonempty) (hIc : I.OrdConnected) :
    timelikeLine.CausalCurveIn ⊤ I id :=
  ⟨hI, hIc, fun a _ b _ => timelikeLine_causalCurveOn_id a b⟩

/-- **Sanity.** On the timelike line, the identity `ℝ → ℝ` is an inextensible causal curve. -/
theorem timelikeLine_inextensible_id : timelikeLine.Inextensible ⊤ univ id :=
  ⟨timelikeLine_causalCurveIn_id ⟨0, trivial⟩ ordConnected_univ,
    fun ⟨_, c', _, _, ⟨t', _, hgrow⟩⟩ => hgrow (c' t') trivial rfl⟩

/-- **Sanity.** On the timelike line, the inclusion `[0, 1] ↪ ℝ` is not inextensible: `[0, 2]`
strictly extends it. -/
theorem timelikeLine_not_inextensible_Icc : ¬ timelikeLine.Inextensible ⊤ (Icc 0 1) id := by
  intro h
  apply h.2
  refine ⟨Icc 0 2, id, timelikeLine_causalCurveIn_id ⟨0, by norm_num, by norm_num⟩
    ordConnected_Icc, ⟨id, strictMonoOn_id, fun t ht => ⟨ht.1, ht.2.trans (by norm_num)⟩, ?_,
    fun _ _ => rfl⟩, ⟨2, ⟨by norm_num, le_rfl⟩, fun t ht h => ?_⟩⟩
  · rw [image_id]; exact ordConnected_Icc
  · have : (2 : ℝ) = t := h
    linarith [ht.2]

/-- A continuous non-decreasing map is a causal curve of the timelike line over every segment. -/
theorem timelikeLine_causalCurveOn_of_monotone {f : ℝ → ℝ} (hf : Monotone f) (hc : Continuous f)
    (a b : ℝ) : timelikeLine.CausalCurveOn ⊤ f a b where
  mem _ _ := trivial
  rel t _ N _ htN := by
    obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 (N.isOpen.mem_nhds htN)
    have hpre : f ⁻¹' Ioo l u ∈ 𝓝 t := hc.continuousAt (Ioo_mem_nhds hl hu)
    obtain ⟨l', u', ⟨hl', hu'⟩, hsub'⟩ := mem_nhds_iff_exists_Ioo_subset.1 hpre
    exact ⟨l', u', hl', hu', fun s _ s' _ h1 h2 h3 => timelikeLine_le.2 ⟨hf h2.le, fun z hz =>
      hsub ⟨(hsub' ⟨h1, h2.trans h3⟩).1.trans_le hz.1,
        hz.2.trans_lt (hsub' ⟨h1.trans h2, h3⟩).2⟩⟩⟩

/-- **Sanity, exercising the reparametrisation.** On the timelike line, `t ↦ min t 0` over `ℝ`
is not inextensible. It is constant on `[0, ∞[`; `φ` (the identity on `]-∞, 0]`, `t ↦ t/(1+t)`
on `[0, ∞[`) squeezes that tail into `[0, 1[`, and `s ↦ min s 0 + max (s - 1) 0` over `ℝ`, which
rises again after `1`, strictly extends it. No extension with `φ = id` exists, since the new curve
would have to stay at `0` on `[0, ∞[`. -/
theorem timelikeLine_not_inextensible_min :
    ¬ timelikeLine.Inextensible ⊤ univ (fun t => min t 0) := by
  intro h
  apply h.2
  set φ : ℝ → ℝ := fun t => min t 0 + max t 0 / (1 + max t 0) with hφ
  set c' : ℝ → ℝ := fun s => min s 0 + max (s - 1) 0 with hc'
  have hden : ∀ t : ℝ, 0 < 1 + max t 0 := fun t => by linarith [le_max_right t 0]
  have hφc : Continuous φ := by
    refine (continuous_id.min continuous_const).add ?_
    exact (continuous_id.max continuous_const).div
      (continuous_const.add (continuous_id.max continuous_const)) fun t => (hden t).ne'
  have hφneg : ∀ {t : ℝ}, t ≤ 0 → φ t = t := fun ht => by
    simp [hφ, min_eq_left ht, max_eq_right ht]
  have hφpos : ∀ {t : ℝ}, 0 ≤ t → φ t = t / (1 + t) := fun ht => by
    simp [hφ, min_eq_right ht, max_eq_left ht]
  have hφmono : StrictMono φ := by
    intro s t hst
    rcases le_or_gt t 0 with ht | ht
    · rw [hφneg ht, hφneg (hst.le.trans ht)]; exact hst
    rcases le_or_gt s 0 with hs | hs
    · rw [hφneg hs, hφpos ht.le]
      have : 0 < t / (1 + t) := div_pos ht (by linarith)
      rcases hs.lt_or_eq with hs | hs
      · linarith
      · rw [hs]; exact this
    · rw [hφpos hs.le, hφpos ht.le, div_lt_div_iff₀ (by linarith) (by linarith)]
      nlinarith
  have hφlt : ∀ t, φ t < 1 := fun t => by
    rcases le_or_gt t 0 with ht | ht
    · rw [hφneg ht]; linarith
    · rw [hφpos ht.le, div_lt_one (by linarith)]; linarith
  have hc'mono : Monotone c' := fun s t hst =>
    add_le_add (min_le_min_right 0 hst) (max_le_max_right 0 (by linarith))
  have hc'c : Continuous c' := by
    simp only [hc']; fun_prop
  refine ⟨univ, c', ⟨⟨0, trivial⟩, ordConnected_univ, fun a _ b _ =>
    timelikeLine_causalCurveOn_of_monotone hc'mono hc'c a b⟩,
    ⟨φ, hφmono.strictMonoOn _, fun _ _ => trivial,
      isPreconnected_iff_ordConnected.1 (isPreconnected_univ.image φ hφc.continuousOn),
      fun t _ => ?_⟩, ⟨2, trivial, fun t _ ht => ?_⟩⟩
  · have h1 : φ t - 1 ≤ 0 := by linarith [hφlt t]
    simp only [hc', max_eq_right h1, add_zero]
    rcases le_or_gt t 0 with ht | ht
    · rw [hφneg ht]
    · rw [hφpos ht.le, min_eq_right (div_pos ht (by linarith)).le, min_eq_right ht.le]
  · have h2 : c' 2 = 1 := by simp only [hc']; norm_num
    rw [h2] at ht
    have : min t 0 ≤ 0 := min_le_right t 0
    linarith

namespace Causality

variable {C : Causality M} {W : Opens M} {I : Set ℝ} {c : ℝ → M}

/-! ### Local relations from causally convex sets -/

/-- In a causally arc-connected spacetime, two causally related points of a causally convex set
`V` (not necessarily open, DEC-7) are related in every open set containing `V`. -/
theorem le_of_causallyConvexIn (hC : C.CausallyArcConnected) {V : Set M} {N : Opens M}
    (hV : C.CausallyConvexIn V ⊤) (hVN : V ⊆ N) {x y : M} (hx : x ∈ V) (hy : y ∈ V)
    (hxy : C.le ⊤ x y) : C.le N x y := by
  obtain ⟨γ, hγ, rfl, rfl⟩ := (hC ⊤ le_rfl x y).1.1 hxy
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ N := fun t ht =>
    hVN (hV.2 _ hx _ hy (mem_diamond.2
      ⟨hγ.le_of_le le_rfl ht.1 ht.2, hγ.le_of_le ht.1 ht.2 le_rfl⟩))
  have hγN : C.CausalCurveOn N γ 0 1 := CurveOn.restrict hγ le_rfl le_rfl le_top hmem
  exact hγN.le_of_le le_rfl zero_le_one le_rfl

/-- In an interval `I ∪ {a}` whose other points lie above `a`, every point above `a` and below a
point of the interval is in `I`. -/
theorem mem_of_insert (hins : (insert a I).OrdConnected) {s σ : ℝ} (hs : s ∈ insert a I)
    (h1 : a < σ) (h2 : σ ≤ s) : σ ∈ I := by
  rcases hins.out (mem_insert a I) hs ⟨h1.le, h2⟩ with h | h
  · exact absurd h (ne_of_gt h1)
  · exact h

/-- If the causal pasts are closed and `c` tends to `p` at the lower end `a` of `I`, then `p` is
in the causal past of every point of the curve. -/
theorem le_of_tendsto (hJ : ∀ x, IsClosed (C.Jminus ⊤ {x})) (hc : C.CausalCurveIn ⊤ I c)
    (haI : ∀ t ∈ I, a < t) (hins : (insert a I).OrdConnected) {p : M}
    (hlim : Tendsto c (𝓝[>] a) (𝓝 p)) {t : ℝ} (ht : t ∈ I) : C.le ⊤ p (c t) := by
  have hmem : p ∈ closure (C.Jminus ⊤ {c t}) := by
    apply mem_closure_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsGT (haI t ht)] with σ hσ
    have hσI : σ ∈ I := mem_of_insert hins (mem_insert_of_mem a ht) hσ.1 hσ.2.le
    simpa using hc.le_of_le hσI ht hσ.2.le
  rw [(hJ (c t)).closure_eq] at hmem
  simpa using hmem

/-! ### Fact 1: adjoining a limit at an open end -/

/-- **A limit at an open end can be adjoined** (`ETT.tex:1291`, first half): if the causal pasts
are closed, `M` strongly causal and causally arc-connected, and `c` tends to `p` at the open lower
end `a` of `I`, then `c` with the value `p` at `a` is a causal curve over `I ∪ {a}`. -/
theorem causalCurveIn_insert (hJ : ∀ x, IsClosed (C.Jminus ⊤ {x})) (hSC : C.StronglyCausal)
    (hC : C.CausallyArcConnected) (hc : C.CausalCurveIn ⊤ I c) {p : M}
    (haI : ∀ t ∈ I, a < t) (hins : (insert a I).OrdConnected)
    (hlim : Tendsto c (𝓝[>] a) (𝓝 p)) :
    C.CausalCurveIn ⊤ (insert a I) (fun t => if t ≤ a then p else c t) := by
  set c₀ : ℝ → M := fun t => if t ≤ a then p else c t with hc₀
  have hc₀a : c₀ a = p := by simp [hc₀]
  have hc₀gt : ∀ {t}, a < t → c₀ t = c t := fun h => by simp [hc₀, not_le.2 h]
  refine ⟨⟨a, mem_insert a I⟩, hins, fun s hs s' hs' => ?_⟩
  rcases le_or_gt s s' with hss' | hss'
  swap
  · exact CurveOn.of_lt hss'
  rcases lt_or_ge a s with has | has
  · -- away from the adjoined point the curve is `c`
    have hsI : s ∈ I := mem_of_insert hins hs has le_rfl
    have hs'I : s' ∈ I := mem_of_insert hins hs' (has.trans_le hss') le_rfl
    exact (hc.curve s hsI s' hs'I).congr fun t ht => (hc₀gt (has.trans_le ht.1)).symm
  -- `s = a`
  have hsa : s = a := by
    rcases hs with h | h
    · exact h
    · exact absurd (haI s h) (not_lt.2 has)
  subst hsa
  refine ⟨fun _ _ => trivial, fun t ht N _ htN => ?_⟩
  rcases eq_or_lt_of_le ht.1 with hts | hts
  · -- at the adjoined point
    subst hts
    have hpN : p ∈ N := by rw [← hc₀a]; exact htN
    obtain ⟨V, hV, hVN, hVc⟩ := hSC p N (N.isOpen.mem_nhds hpN)
    obtain ⟨δ, hδ, hδV⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hlim hV)
    refine ⟨s - 1, δ, by linarith, hδ, fun σ hσ σ' hσ' h1 h2 h3 => ?_⟩
    have hσ'a : s < σ' := hσ.1.trans_lt h2
    have hσ'I : σ' ∈ I := mem_of_insert hins hs' hσ'a hσ'.2
    have hσ'V : c σ' ∈ V := hδV ⟨hσ'a, h3⟩
    rw [hc₀gt hσ'a]
    rcases eq_or_lt_of_le hσ.1 with hσs | hσs
    · subst hσs
      rw [hc₀a]
      exact le_of_causallyConvexIn hC hVc hVN (mem_of_mem_nhds hV) hσ'V
        (le_of_tendsto hJ hc haI hins hlim hσ'I)
    · have hσI : σ ∈ I := mem_of_insert hins hs' hσs hσ.2
      rw [hc₀gt hσs]
      exact le_of_causallyConvexIn hC hVc hVN (hδV ⟨hσs, h2.trans h3⟩) hσ'V
        (hc.le_of_le hσI hσ'I h2.le)
  · -- above the adjoined point
    set ε := (s + t) / 2 with hε
    have hsε : s < ε := by rw [hε]; linarith
    have hεt : ε < t := by rw [hε]; linarith
    have hεI : ε ∈ I := mem_of_insert hins hs' hsε (hεt.le.trans ht.2)
    have hs'I : s' ∈ I := mem_of_insert hins hs' (hts.trans_le ht.2) le_rfl
    have hctN : c t ∈ N := by rw [← hc₀gt hts]; exact htN
    obtain ⟨l, u, hl, hu, hrel⟩ :=
      (hc.curve ε hεI s' hs'I).rel t ⟨hεt.le, ht.2⟩ N le_top hctN
    refine ⟨max l ε, u, max_lt hl hεt, hu, fun σ hσ σ' hσ' h1 h2 h3 => ?_⟩
    have hεσ : ε < σ := (le_max_right _ _).trans_lt h1
    rw [hc₀gt (hsε.trans hεσ), hc₀gt (hsε.trans (hεσ.trans h2))]
    exact hrel σ ⟨hεσ.le, hσ.2⟩ σ' ⟨(hεσ.trans h2).le, hσ'.2⟩
      ((le_max_left _ _).trans_lt h1) h2 h3

/-! ### Fact 2: prepending at a closed end -/

/-- **Prepending** a causal curve from `q` to the first point of `c`. -/
theorem exists_prepend (hC : C.CausallyArcConnected) (hc : C.CausalCurveIn W I c)
    (ha : IsLeast I a) {q : M} (hq : C.le W q (c a)) :
    ∃ c' : ℝ → M, C.CausalCurveIn W (Icc (a - 1) a ∪ I) c' ∧ (∀ t ∈ I, c' t = c t) ∧
      c' (a - 1) = q := by
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := (hC W le_top q (c a)).1.1 hq
  set γ' : ℝ → M := fun t => γ (1 * t + -(a - 1)) with hγ'
  have hγ'c : C.CausalCurveOn W γ' (a - 1) a :=
    CurveOn.comp_affine (k := 1) (m := -(a - 1)) one_pos (by
      have h1 : (1 : ℝ) * (a - 1) + -(a - 1) = 0 := by ring
      have h2 : (1 : ℝ) * a + -(a - 1) = 1 := by ring
      rw [h1, h2]; exact hγ)
  have hγ'a : γ' a = c a := by
    rw [hγ']; simp only
    rw [show (1 : ℝ) * a + -(a - 1) = 1 by ring, hγ1]
  have hγ'0 : γ' (a - 1) = q := by
    rw [hγ']; simp only
    rw [show (1 : ℝ) * (a - 1) + -(a - 1) = 0 by ring, hγ0]
  set c' : ℝ → M := fun t => if t ≤ a then γ' t else c t with hc'
  have hle : ∀ {t}, t ≤ a → c' t = γ' t := fun h => by simp [hc', h]
  have hgt : ∀ {t}, a < t → c' t = c t := fun h => by simp [hc', not_le.2 h]
  have hmemI : ∀ {t}, a < t → t ∈ Icc (a - 1) a ∪ I → t ∈ I := fun h ht => by
    rcases ht with ht | ht
    · exact absurd ht.2 (not_le.2 h)
    · exact ht
  have hge : ∀ {t}, t ∈ Icc (a - 1) a ∪ I → a - 1 ≤ t := fun ht => by
    rcases ht with ht | ht
    · exact ht.1
    · linarith [ha.2 ht]
  refine ⟨c', ⟨⟨a, Or.inr ha.1⟩, ⟨fun x hx y hy z hz => ?_⟩, fun s hs s' hs' => ?_⟩, fun t ht => ?_,
    by rw [hle (by linarith), hγ'0]⟩
  · -- the union is an interval
    rcases le_or_gt z a with hza | hza
    · exact Or.inl ⟨(hge hx).trans hz.1, hza⟩
    · exact Or.inr (hc.ordConnected.out ha.1 (hmemI (hza.trans_le hz.2) hy) ⟨hza.le, hz.2⟩)
  · rcases le_or_gt s s' with hss' | hss'
    swap
    · exact CurveOn.of_lt hss'
    rcases le_or_gt s' a with hs'a | hs'a
    · exact (CurveOn.restrict hγ'c (hge hs) hs'a le_rfl
        (fun t ht => hγ'c.mem t ⟨(hge hs).trans ht.1, ht.2.trans hs'a⟩)).congr
        fun t ht => (hle (ht.2.trans hs'a)).symm
    rcases le_or_gt s a with hsa | hsa
    · have h₁ : C.CausalCurveOn W γ' s a := CurveOn.restrict hγ'c (hge hs) le_rfl le_rfl
        (fun t ht => hγ'c.mem t ⟨(hge hs).trans ht.1, ht.2⟩)
      exact CurveOn.concat C.isRelFamily_le h₁ (hc.curve a ha.1 s' (hmemI hs'a hs')) hsa
        hs'a.le hγ'a
    · exact (hc.curve s (hmemI hsa hs) s' (hmemI (hsa.trans_le hss') hs')).congr
        fun t ht => (hgt (hsa.trans_le ht.1)).symm
  · rcases eq_or_lt_of_le (ha.2 ht) with h | h
    · rw [← h, hle le_rfl, hγ'a]
    · exact hgt h

/-- From `x ∈ s`, `s ≠ {x}`: another point of `s`. -/
theorem exists_ne_of_ne_singleton {α : Type*} {s : Set α} {x : α} (hx : x ∈ s) (h : s ≠ {x}) :
    ∃ y ∈ s, y ≠ x := by
  by_contra h'
  refine h (eq_singleton_iff_unique_mem.2 ⟨hx, fun y hy => ?_⟩)
  by_contra hne
  exact h' ⟨y, hy, hne⟩

/-- **Fact 2** (`ETT.tex:1292–1294`): in a causally arc-connected causal spacetime, a curve over
an interval with a least point `a` and `J^-_W(c a) ≠ {c a}` is extensible, by prepending. -/
theorem extensible_of_isLeast (hC : C.CausallyArcConnected) (hcaus : C.IsCausal)
    (hc : C.CausalCurveIn W I c) (ha : IsLeast I a) (hJ : C.Jminus W {c a} ≠ {c a}) :
    C.Extensible W I c := by
  obtain ⟨q, hqJ, hqne⟩ := exists_ne_of_ne_singleton
    (by simpa using C.le_refl (hc.mem ha.1) : c a ∈ C.Jminus W {c a}) hJ
  have hq : C.le W q (c a) := by simpa using hqJ
  obtain ⟨c', hc', heq, h0⟩ := exists_prepend hC hc ha hq
  refine ⟨_, c', hc', ⟨id, strictMonoOn_id, fun t ht => Or.inr ht, by
    rw [image_id]; exact hc.ordConnected, fun t ht => heq t ht⟩,
    ⟨a - 1, Or.inl ⟨le_rfl, by linarith⟩, fun t ht hqt => ?_⟩⟩
  rw [h0] at hqt
  subst hqt
  exact hqne (hcaus (C.le_mono le_top hq) (C.le_mono le_top (hc.le_of_le ha.1 ht (ha.2 ht))))

/-- Fact 2, at the future end: appending at a greatest point. -/
theorem extensible_of_isGreatest (hC : C.CausallyArcConnected) (hcaus : C.IsCausal)
    (hc : C.CausalCurveIn W I c) (hb : IsGreatest I b) (hJ : C.Jplus W {c b} ≠ {c b}) :
    C.Extensible W I c := by
  apply Extensible.of_dual_reverse
  refine extensible_of_isLeast (dual_causallyArcConnectedOn.2 hC) (dual_isCausal.2 hcaus)
    hc.reverse (a := -b) ⟨by simpa using hb.1, fun t ht => ?_⟩ ?_
  · have := hb.2 (show -t ∈ I from ht)
    linarith
  · simpa using hJ

/-- **Fact 1, as the sketch uses it** (`ETT.tex:1291–1294`): a curve with a limit `p` at an open
lower end is extensible, when the causal pasts are closed, `M` is strongly causal, causally
arc-connected and causal, and `J^-(p) ≠ {p}`: adjoin `p`, then prepend. -/
theorem extensible_of_tendsto (hJ : ∀ x, IsClosed (C.Jminus ⊤ {x})) (hSC : C.StronglyCausal)
    (hC : C.CausallyArcConnected) (hcaus : C.IsCausal) (hc : C.CausalCurveIn ⊤ I c)
    {p : M} (haI : ∀ t ∈ I, a < t) (hins : (insert a I).OrdConnected)
    (hlim : Tendsto c (𝓝[>] a) (𝓝 p)) (hp : C.Jminus ⊤ {p} ≠ {p}) : C.Extensible ⊤ I c := by
  have h₀ := causalCurveIn_insert hJ hSC hC hc haI hins hlim
  obtain ⟨q, hqJ, hqne⟩ := exists_ne_of_ne_singleton
    (by simpa using C.le_refl (show p ∈ (⊤ : Opens M) from trivial) : p ∈ C.Jminus ⊤ {p}) hp
  have hq : C.le ⊤ q p := by simpa using hqJ
  have hleast : IsLeast (insert a I) a := ⟨mem_insert a I, fun t ht => by
    rcases ht with h | h
    · exact h.ge
    · exact (haI t h).le⟩
  obtain ⟨c', hc', heq, h0⟩ := exists_prepend hC h₀ hleast (q := q) (by simpa using hq)
  have hcI : ∀ t ∈ I, c' t = c t := fun t ht => by
    rw [heq t (mem_insert_of_mem a ht)]
    simp [not_le.2 (haI t ht)]
  refine ⟨_, c', hc', ⟨id, strictMonoOn_id, fun t ht => Or.inr (mem_insert_of_mem a ht), by
    rw [image_id]; exact hc.ordConnected, hcI⟩,
    ⟨a - 1, Or.inl ⟨le_rfl, by linarith⟩, fun t ht hqt => ?_⟩⟩
  rw [h0] at hqt
  subst hqt
  exact hqne (hcaus hq (le_of_tendsto hJ hc haI hins hlim ht))

/-- **Fact 2, one-sided** (DEC-13): prepending is an extension at the past end. -/
theorem pastExtensible_of_isLeast (hC : C.CausallyArcConnected) (hcaus : C.IsCausal)
    (hc : C.CausalCurveIn W I c) (ha : IsLeast I a) (hJ : C.Jminus W {c a} ≠ {c a}) :
    C.PastExtensible W I c := by
  obtain ⟨q, hqJ, hqne⟩ := exists_ne_of_ne_singleton
    (by simpa using C.le_refl (hc.mem ha.1) : c a ∈ C.Jminus W {c a}) hJ
  have hq : C.le W q (c a) := by simpa using hqJ
  obtain ⟨c', hc', heq, h0⟩ := exists_prepend hC hc ha hq
  refine ⟨_, c', hc', ⟨id, strictMonoOn_id, fun t ht => Or.inr ht, by
    rw [image_id]; exact hc.ordConnected, fun t ht => heq t ht, ?_⟩,
    ⟨a - 1, Or.inl ⟨le_rfl, by linarith⟩, fun t ht hqt => ?_⟩⟩
  · intro t ht t' ht' htt'
    rcases ht' with ht' | ht'
    · have : t' = a := le_antisymm ht'.2 ((ha.2 ht).trans htt')
      exact ⟨t', this ▸ ha.1, rfl⟩
    · exact ⟨t', ht', rfl⟩
  · rw [h0] at hqt
    subst hqt
    exact hqne (hcaus (C.le_mono le_top hq) (C.le_mono le_top (hc.le_of_le ha.1 ht (ha.2 ht))))

/-- **Fact 1 as the sketch uses it, one-sided** (DEC-13): adjoining the limit at the open lower
end and prepending is an extension at the past end. -/
theorem pastExtensible_of_tendsto (hJ : ∀ x, IsClosed (C.Jminus ⊤ {x})) (hSC : C.StronglyCausal)
    (hC : C.CausallyArcConnected) (hcaus : C.IsCausal) (hc : C.CausalCurveIn ⊤ I c)
    {p : M} (haI : ∀ t ∈ I, a < t) (hins : (insert a I).OrdConnected)
    (hlim : Tendsto c (𝓝[>] a) (𝓝 p)) (hp : C.Jminus ⊤ {p} ≠ {p}) :
    C.PastExtensible ⊤ I c := by
  have h₀ := causalCurveIn_insert hJ hSC hC hc haI hins hlim
  obtain ⟨q, hqJ, hqne⟩ := exists_ne_of_ne_singleton
    (by simpa using C.le_refl (show p ∈ (⊤ : Opens M) from trivial) : p ∈ C.Jminus ⊤ {p}) hp
  have hq : C.le ⊤ q p := by simpa using hqJ
  have hleast : IsLeast (insert a I) a := ⟨mem_insert a I, fun t ht => by
    rcases ht with h | h
    · exact h.ge
    · exact (haI t h).le⟩
  obtain ⟨c', hc', heq, h0⟩ := exists_prepend hC h₀ hleast (q := q) (by simpa using hq)
  have hcI : ∀ t ∈ I, c' t = c t := fun t ht => by
    rw [heq t (mem_insert_of_mem a ht)]
    simp [not_le.2 (haI t ht)]
  refine ⟨_, c', hc', ⟨id, strictMonoOn_id, fun t ht => Or.inr (mem_insert_of_mem a ht), by
    rw [image_id]; exact hc.ordConnected, hcI, ?_⟩,
    ⟨a - 1, Or.inl ⟨le_rfl, by linarith⟩, fun t ht hqt => ?_⟩⟩
  · intro t ht t' ht' htt'
    have hat' : a < t' := (haI t ht).trans_le htt'
    rcases ht' with ht' | ht'
    · exact absurd ht'.2 (not_le.2 hat')
    · rcases ht' with h | h
      · exact absurd h (ne_of_gt hat')
      · exact ⟨t', h, rfl⟩
  · rw [h0] at hqt
    subst hqt
    exact hqne (hcaus hq (le_of_tendsto hJ hc haI hins hlim ht))

end Causality


end Causal
