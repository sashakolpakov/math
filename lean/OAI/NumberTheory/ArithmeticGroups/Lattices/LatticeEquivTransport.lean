import OAI.NumberTheory.ArithmeticGroups.Lattices.OpenHomQuotient
import OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.KernelDiscrete

/-! # Lattice Equiv Transport -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeEquivTransport.Construction

noncomputable section

section

/-! Lattices pull back through continuous open surjective homomorphisms
with finite kernel, using the actual quotient homeomorphism. -/

open _root_.MeasureTheory

theorem lattice_comap_of_open_surjective_finite_kernel
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (f : G →* H) (hsurj : Function.Surjective f) (hf : Continuous f) (hopen : IsOpenMap f)
    [Finite f.ker] (Γ : Subgroup H) (hΓ : IntegralLattice.IsLattice Γ) : IntegralLattice.IsLattice (Γ.comap f) := by
  let : MeasurableSpace (G ⧸ Γ.comap f) := borel (G ⧸ Γ.comap f)
  let : BorelSpace (G ⧸ Γ.comap f) := ⟨rfl⟩
  let : MeasurableSpace (H ⧸ Γ) := borel (H ⧸ Γ)
  let : BorelSpace (H ⧸ Γ) := ⟨rfl⟩
  obtain ⟨hdisc, μ, hμprob, hμinv⟩ := hΓ
  let : DiscreteTopology Γ := hdisc
  let : DiscreteTopology (Γ.comap f) := Lattices.Finite.KernelDiscrete.Construction.discrete_comap_of_finite_kernel f hf Γ
  let e := OpenHomQuotient.Construction.openHomComapCosetHomeomorph f hsurj hf hopen Γ
  have he : ∀ (g : G) (x : G ⧸ Γ.comap f), e (g • x) = f g • e x := by
    intro g x
    obtain ⟨x, rfl⟩ := Quotient.exists_rep x
    change QuotientGroup.mk (f (g * x)) = (QuotientGroup.mk (f g * f x) : H ⧸ Γ)
    rw [map_mul]
  have hei : ∀ (g : G) (y : H ⧸ Γ), e.symm (f g • y) = g • e.symm y := by
    intro g y
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  let : SMulInvariantMeasure G (G ⧸ Γ.comap f) (μ.map e.symm) := by
    constructor
    intro g s hs
    rw [Measure.map_apply e.symm.measurable (hs.preimage (measurable_const_smul g)),
      Measure.map_apply e.symm.measurable hs]
    have hp : e.symm ⁻¹' ((g • ·) ⁻¹' s) = (f g • ·) ⁻¹' (e.symm ⁻¹' s) := by
      ext y
      simp only [Set.mem_preimage, hei]
    rw [hp]
    exact SMulInvariantMeasure.measure_preimage_smul (f g) (hs.preimage e.symm.measurable)
  exact ⟨inferInstance, μ.map e.symm,
    inferInstance, inferInstance⟩

end

/-! The lattice property pulls back through a topological group equivalence. -/

theorem lattice_of_continuous_equiv_map
    {H K : Type*} [Group H] [Group K] [TopologicalSpace H] [TopologicalSpace K]
    [IsTopologicalGroup H] [IsTopologicalGroup K] [T2Space H]
    (e : H ≃ₜ* K) (Γ : Subgroup H) (hΓ : IntegralLattice.IsLattice (Γ.map e.toMonoidHom)) : IntegralLattice.IsLattice Γ := by
  let f := e.toMonoidHom
  let : Subsingleton f.ker := ⟨fun x y => Subtype.ext (e.injective (x.property.trans y.property.symm))⟩
  let : Finite f.ker := inferInstance
  have ht := lattice_comap_of_open_surjective_finite_kernel f e.surjective e.continuous e.isOpenMap _ hΓ
  have he : (Γ.map f).comap f = Γ := by
    ext g
    constructor
    · rintro ⟨x, hx, he⟩
      exact e.injective he ▸ hx
    · intro hg
      exact ⟨g, hg, rfl⟩
  rwa [he] at ht

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeEquivTransport.Construction
