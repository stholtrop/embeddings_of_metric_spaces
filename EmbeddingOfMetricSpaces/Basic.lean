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

lemma diameterIsAttained [MetricSpace X] (S : Set X) (hS : IsCompact S) (ne_S : S.Nonempty) : ∃ w ∈ S, ∃ z ∈  S, dist w z = Metric.diam (S) := by
  have := IsCompact.prod hS hS
  rcases this.exists_isMaxOn (ne_S.prod ne_S) continuous_dist.continuousOn with ⟨x, hx, hhx⟩
  use x.1, hx.1, x.2, hx.2
  rw [isMaxOn_iff] at hhx
  have : ∀ x1 ∈ S, ∀ x2 ∈ S, dist x1 x2 ≤ dist x.1 x.2 := by
    intro x1 hx1 x2 hx2
    specialize hhx ⟨x1, x2⟩ ⟨hx1, hx2⟩
    exact hhx
  have ineq1 := Metric.diam_le_of_forall_dist_le_of_nonempty ne_S this
  have ineq2 := Metric.dist_le_diam_of_mem hS.isBounded hx.1 hx.2
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
  have : ∀ a ∈  g ⁻¹' {y}, ∀ b ∈ g ⁻¹' {y}, dist a b < ε := by
    intro a ha b hb
    apply hδ a b
    calc
      dist (f a) (f b) ≤ dist (f a) (g a) + dist (g a) (f b) := dist_triangle (f a) (g a) (f b)
      _ ≤ dist (f a) (g a) + (dist (g a) (g b) + dist (g b) (f b)) := by
        gcongr
        exact dist_triangle (g a) (g b) (f b)
      _ = dist (f a) (g a) + dist (g b) (f b) := by
        rw [add_left_cancel_iff]
        conv_rhs => rw [← zero_add (dist (g b) (f b))]
        rw [add_right_cancel_iff]
        rw [dist_eq_zero]
        have ha : g a = y := by
          rw [← Set.mem_singleton_iff]
          rw [← Set.mem_preimage]
          exact ha
        have hb : g b = y := by
          rw [← Set.mem_singleton_iff]
          rw [← Set.mem_preimage]
          exact hb
        rw [ha, hb]
      _ < δ := by
        have dfgest : ∀ (x : X), dist (f x) (g x) < δ / 2 := by
          have : δ / 2 > 0 := by linarith
          rw [← ContinuousMap.dist_lt_iff this]
          rw [← Metric.mem_ball']
          exact hg
        suffices h : dist (f a) (g a) < δ / 2 ∧ dist (g b) (f b )< δ / 2  by
          obtain ⟨hha, hhb⟩ := h
          linarith
        constructor
        exact dfgest a
        rw [dist_comm]
        exact dfgest b
  have cpt_fibs : IsCompact (g ⁻¹' {y}) := by
    apply IsClosed.isCompact
    apply IsClosed.preimage g.2
    apply isClosed_singleton
  -- rw [isCompact_iff_compactSpace] at cpt_fibs
  obtain (h | h) := isEmpty_or_nonempty (g ⁻¹' {y})
  have : Metric.diam (g ⁻¹' {y}) = 0 := by
    rw [Set.isEmpty_coe_sort.mp h]
    simp
  linarith
  rw [Set.nonempty_coe_sort] at h
  have tmp : ∃ w ∈ g ⁻¹' {y}, ∃ z ∈ g ⁻¹' {y}, dist w z = Metric.diam (g ⁻¹' {y}) := diameterIsAttained X (g ⁻¹' {y}) cpt_fibs h
  rcases tmp with ⟨w, hw, z, hz, hwz⟩
  specialize this w hw z hz
  rw [← hwz]
  exact this

lemma epsilonInjective_to_injective [MetricSpace X] [MetricSpace Y] (f : X → Y) (hf : ∀ ε > 0, epsilonInjective f ε) : f.Injective := by
  intro a b hhf
  rw [← zero_eq_dist]

  have : ∀ ε > 0 , dist a b < 0 + ε := by
    intro ε hε
    have ⟨hbound, bound⟩ := hf ε hε (f a)
    have ha : a ∈ f ⁻¹' {f a} := by simp
    have hb : b ∈ f ⁻¹' {f a} := by
      rw [hhf]
      simp
    have := Metric.dist_le_diam_of_mem hbound ha hb
    linarith

  exact le_antisymm (dist_nonneg (x := a) (y := b)) (le_of_forall_pos_lt_add this)
