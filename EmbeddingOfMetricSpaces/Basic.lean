import Mathlib

/-!
# Embeddings of finite dimensional metric spaces
This files proves that any finite dimensional compact metric spaces admits
an embedding into R^{2n+1}
-/


variable {X Y : Type*}

def epsilonInjective [MetricSpace X] [MetricSpace Y] (f : X → Y) (ε : ℝ) : Prop :=
∀ y , Bornology.IsBounded (f ⁻¹' {y}) ∧ Metric.diam (f ⁻¹' {y}) < ε

/-
TODO:
- Define space of epsilon embeddings as a subspace of continuous functions with uniform topology.
- Show the space of epsilon embeddings is open
- Show the space of epsilon embeddings is dense under the right assumptions
- Define general position
-/


lemma stabilityOfEpsilonInjective [MetricSpace X] [CompactSpace X] [MetricSpace Y] (f : X → Y) (hf1 : Continuous f) (ε : ℝ) (hf2 : epsilonInjective f ε) : ∃ δ > 0 , ∀ x y , dist (f x) (f y) < δ → dist x y < ε := by
  by_contra h
  simp at h
  have seqs_exists : ∀ (n : ℕ ), ∃ (a1 : X) (a2 : X), (dist (f a1) (f a2) < (1/2)^n) ∧ (ε ≤ dist a1 a2) := by
    intro n
    apply h ((1/2)^n)
    simp
  choose a1 a2 hd1 hd2 using seqs_exists
  rcases CompactSpace.tendsto_subseq a1 with ⟨la1, φ, hφ, hla1⟩
  rcases CompactSpace.tendsto_subseq (a2 ∘ φ) with ⟨la2, ψ, hψ, hla2⟩

  let hla12 := hla1.comp hψ.tendsto_atTop

  let fhla1 := (Continuous.seqContinuous hf1 hla1).comp hψ.tendsto_atTop
  let fhla2 := Continuous.seqContinuous hf1 hla2

  let difference : (ℕ → ℝ) :=
    fun n ↦ Dist.dist (f <| a1 <| φ <| ψ n) (f ∘ a2 ∘ φ ∘ ψ <| n)

  have hdifference : Filter.Tendsto difference Filter.atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have test := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ ) ≤ 1/2) (by norm_num : 1/2 < ( 1 : ℝ ))
    rw [Metric.tendsto_atTop] at test
    let ⟨ N , hN ⟩:= test ε hε
    use N
    intro n hn
    rw [Real.dist_0_eq_abs]
    have : N ≤ (φ <| ψ <| N) := (StrictMono.comp hφ hψ).le_apply
    have : N ≤ (φ <| ψ <| n) := this.trans (hφ.monotone (hψ.monotone hn))
    specialize hN (φ <| ψ <| n) this
    rw [Real.dist_0_eq_abs] at hN
    specialize hd1 (φ <| ψ <| n )
    simp [difference]
    grind
  have hconvergence : Filter.Tendsto difference Filter.atTop (nhds (dist (f la1) (f la2))) := by
    let temporary_product := fun n ↦ (f <| a1 <| φ <| ψ <| n, f <| a2 <| φ <| ψ <| n)
    have : (fun n ↦ (temporary_product n).1) = (f ∘  a1 ∘  φ ∘  ψ) := rfl
    erw [← this] at fhla1
    have : (fun n ↦ (temporary_product n).2) = (f ∘  a2 ∘  φ ∘  ψ) := rfl
    erw [← this] at fhla2
    have temporary_filter := Filter.tendsto_prod_iff'.mpr ⟨fhla1, fhla2⟩
    rw [← nhds_prod_eq] at temporary_filter
    have := Continuous.tendsto continuous_dist (f la1, f la2)
    have := this.comp temporary_filter
    unfold difference
    unfold temporary_product at this
    exact this
  have := tendsto_nhds_unique hdifference hconvergence
  have := eq_of_dist_eq_zero this.symm
  have hdistance : dist la1 la2 < ε := by
    have hhla2 : la2 ∈ f⁻¹' {f la1} := by
      rw [this]
      rfl
    have hhla1 : la1 ∈ f⁻¹' {f la1} := by rfl
    obtain ⟨bdd, epsbd⟩ := hf2 (f la1)
    have b := Metric.dist_le_diam_of_mem bdd hhla1 hhla2
    linarith
  have hlowerBound : dist la1 la2 ≥ ε := by
    let temporary_product := fun n ↦ (a1 <| φ <| ψ <| n, a2 <| φ <| ψ <| n)
    have : (fun n ↦ (temporary_product n).1) = ( a1 ∘  φ ∘  ψ) := rfl
    erw [← this] at hla12
    have : (fun n ↦ (temporary_product n).2) = (  a2 ∘  φ ∘  ψ) := rfl
    erw [← this] at hla2
    have temporary_filter := Filter.tendsto_prod_iff'.mpr ⟨hla12, hla2⟩
    rw [← nhds_prod_eq] at temporary_filter
    have := Continuous.tendsto continuous_dist (la1, la2)
    have := this.comp temporary_filter
    unfold temporary_product at this
    unfold Function.comp at this
    simp at this
    have subseqbound : ∀ (n : ℕ ), ε ≤ dist (a1 <| φ <| ψ <| n) (a2 <| φ <| ψ <| n) := by
      intro n
      exact hd2 (φ <| ψ <| n)
    exact ge_of_tendsto' this subseqbound
  linarith

variable (X Y)

def spaceOfEpsilonInjective [MetricSpace X] [CompactSpace X] [MetricSpace Y] (ε : ℝ) := {f : C(X, Y) | epsilonInjective f ε}

lemma epsilonInjectiveMonotone [MetricSpace X] [MetricSpace Y] (f : X → Y) (ε : ℝ) (δ : ℝ ) (hδ : ε < δ) (hf : epsilonInjective f ε) : epsilonInjective f δ := by
  simp [epsilonInjective] at hf ⊢
  intro y
  specialize hf y
  constructor
  exact hf.1
  linarith

lemma epsilonInjectiveOpen [MetricSpace X] [CompactSpace X] [MetricSpace Y] (ε : ℝ) (hε : ε > 0) : IsOpen (spaceOfEpsilonInjective X Y ε) := by
  rw [Metric.isOpen_iff]
  intro f hf
  unfold spaceOfEpsilonInjective at hf
  simp at hf
  obtain ⟨δ, hhδ, hδ⟩ := stabilityOfEpsilonInjective f f.2 ε hf
  use δ/2
  constructor
  linarith
  intro g hg
  simp [spaceOfEpsilonInjective, epsilonInjective]
  intro y
  constructor
  exact Metric.isBounded_of_compactSpace
  --apply Metric.diam_le_of_forall_dist_lt

  sorry








--




  -- ∃ (a1 : ℕ → X) (a2 : ℕ → X), ∀ n , dist (f (a1 n)) (f (a2 n)) < 1/n ∧ dist (a1 n) (a2 n) < ε := by



sorry
