import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.Center
import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.TangentCenter

/-! # Tangent -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! The actual glued finite-order surface center is smooth, permissible, and nonzero. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}
    (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (ℓ : ℕ)
    (C : ∀ i, Surface.TangentCenterChoice.Construction.SurfaceTangentCenterChoice ℂ (A.rings i) (A.ideals i) n ℓ)
    (I : X.IdealSheafData) (hI : ∀ i, I.comap (A.map i) = Affine.QuotientKernel.Construction.affineQuotientKernel (C i).center)

include hI

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.surfaceCenter_ideal (i : A.indices) : I.ideal (A.nativeOpens i) =
    (C i).center.comap (Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv (A.rings i) (A.map i)).toRingHom :=
  Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv_ideal (A.rings i) (A.map i) I _ (hI i)

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.surfaceCenter_permissible (hdim : ∀ i, ringKrullDim (A.rings i) ≤ 2)
    (hlevel : (n + 1).factorial ≤ ℓ + 1) : J ≤ I ^ (n + 1) := by
  apply GlobalComponent.Center.Construction.idealSheaf_le_of_native_affine_cover A.nativeOpens A.nativeOpens_cover
  intro i
  change J.ideal (A.nativeOpens i) ≤ I.ideal (A.nativeOpens i) ^ (n + 1)
  rw [A.surfaceCenter_ideal ℓ C I hI i, Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv_ideal (A.rings i) (A.map i) J _ (A.ideal_eq i)]
  rw [← IdealSheaf.ColonRestriction.Construction.ideal_comap_pow_of_bijective (Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv (A.rings i) (A.map i)).toRingHom
    (Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv (A.rings i) (A.map i)).bijective]
  exact Ideal.comap_mono ((C i).permissible (hdim i) hlevel)

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.surfaceCenter_smooth (hdim : ∀ i, ringKrullDim (A.rings i) ≤ 2)
    (hlevel : (n + 1).factorial ≤ ℓ + 1) : Smooth (I.subschemeι ≫ f) := by
  apply Global.MonomialBoundaryAtlas.Construction.idealSheaf_complex_center_smooth_of_chosen_affine_cover f I A.nativeOpens A.nativeOpens_cover
  intro i
  let : Algebra ℂ Γ(X, A.nativeOpens i) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.nativeOpens i)
  let e := Affine.OpenBoundaryTransport.Construction.specOpenSectionAlgEquiv f (A.rings i) (A.map i) (A.ground i)
  rw [A.surfaceCenter_ideal ℓ C I hI i]
  let : Algebra.Smooth ℂ (A.rings i ⧸ (C i).center) := (C i).center_smooth (hdim i) hlevel
  exact Algebra.Smooth.of_equiv (Ideal.quotientEquivAlg (C i).center _ e.symm
    (Ideal.map_symm e.toRingEquiv).symm)

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.surfaceCenter_ne_bot [Nonempty X] : I ≠ ⊥ := by
  intro hz
  let x : X := Classical.choice inferInstance
  have hx : x ∈ ⨆ i, (A.map i).opensRange := by rw [A.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨q, _⟩ := hi
  let : q.asIdeal.IsPrime := q.isPrime
  let : Nontrivial (A.rings i) := (algebraMap (A.rings i) q.asIdeal.ResidueField).domain_nontrivial
  have he : I.ideal (A.nativeOpens i) = ⊥ := by rw [hz]; rfl
  rw [A.surfaceCenter_ideal ℓ C I hI i] at he
  have hm := congrArg (Ideal.map (Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv (A.rings i) (A.map i)).toRingHom) he
  rw [Ideal.map_comap_of_surjective (Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv (A.rings i) (A.map i)).toRingHom
    (Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv (A.rings i) (A.map i)).surjective, Ideal.map_bot] at hm
  exact (C i).center_ne_bot hm

end

end OAI.AlgebraicGeometry.Resolution.Blowups
