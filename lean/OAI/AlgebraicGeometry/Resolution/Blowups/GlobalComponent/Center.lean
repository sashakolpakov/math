import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.ChoiceAtlas
import OAI.AlgebraicGeometry.Resolution.Blowups.Component.Choice
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.FlatBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.MapGluing

/-! # Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent

noncomputable section

/-! The glued canonical component center is smooth, permissible, nonzero, and has an isomorphic ambient blowup. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem Center.Construction.idealSheaf_le_of_native_affine_cover {X : Scheme} {ι : Type}
    (U : ι → X.affineOpens) (hcover : ⨆ i, (U i).val = ⊤)
    (I J : X.IdealSheafData) (h : ∀ i, I.ideal (U i) ≤ J.ideal (U i)) : I ≤ J := by
  apply inf_eq_left.mp
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U hcover
  intro i
  exact inf_eq_left.mpr (h i)

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {n : ℕ}

def ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.center (A : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) : X.IdealSheafData :=
  A.existsUnique_center.choose

theorem ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.center_restrict (A : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (i : A.indices) :
    A.center.comap (A.map i) = Affine.QuotientKernel.Construction.affineQuotientKernel (A.choice i).center :=
  A.existsUnique_center.choose_spec.1 i

abbrev ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.nativeOpens (A : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (i : A.indices) : X.affineOpens :=
  Affine.OpenBoundaryTransport.Construction.specOpenImage (A.rings i) (A.map i)

theorem ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.nativeOpens_cover (A : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) :
    (⨆ i, (A.nativeOpens i).val) = ⊤ := by
  simp only [ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.nativeOpens, Affine.OpenBoundaryTransport.Construction.specOpenImage_eq_opensRange]
  exact A.cover

theorem ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.center_ideal (A : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (i : A.indices) :
    A.center.ideal (A.nativeOpens i) =
      (A.choice i).center.comap (Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv (A.rings i) (A.map i)).toRingHom :=
  Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv_ideal (A.rings i) (A.map i) A.center _ (A.center_restrict i)

theorem ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.center_permissible (A : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) : J ≤ A.center ^ (n + 1) := by
  apply Center.Construction.idealSheaf_le_of_native_affine_cover A.nativeOpens A.nativeOpens_cover
  intro i
  change J.ideal (A.nativeOpens i) ≤ A.center.ideal (A.nativeOpens i) ^ (n + 1)
  rw [A.center_ideal i, Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv_ideal (A.rings i) (A.map i) J _ (A.ideal_eq i)]
  rw [← IdealSheaf.ColonRestriction.Construction.ideal_comap_pow_of_bijective (Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv (A.rings i) (A.map i)).toRingHom
    (Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv (A.rings i) (A.map i)).bijective]
  exact Ideal.comap_mono (A.choice i).permissible

theorem ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.center_smooth (A : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) : Smooth (A.center.subschemeι ≫ f) := by
  apply Global.MonomialBoundaryAtlas.Construction.idealSheaf_complex_center_smooth_of_chosen_affine_cover f A.center A.nativeOpens A.nativeOpens_cover
  intro i
  let : Algebra ℂ Γ(X, A.nativeOpens i) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.nativeOpens i)
  let e := Affine.OpenBoundaryTransport.Construction.specOpenSectionAlgEquiv f (A.rings i) (A.map i) (A.ground i)
  rw [A.center_ideal i]
  let : Algebra.Smooth ℂ (A.rings i ⧸ (A.choice i).center) := (A.choice i).center_smooth
  exact Algebra.Smooth.of_equiv (Ideal.quotientEquivAlg (A.choice i).center _ e.symm
    (Ideal.map_symm e.toRingEquiv).symm)

theorem ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.center_ne_bot [Nonempty X] (A : ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) : A.center ≠ ⊥ := by
  intro hzero
  let x : X := Classical.choice inferInstance
  have hx : x ∈ ⨆ i, (A.map i).opensRange := by rw [A.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨q, _⟩ := hi
  let : q.asIdeal.IsPrime := q.isPrime
  let : Nontrivial (A.rings i) := (algebraMap (A.rings i) q.asIdeal.ResidueField).domain_nontrivial
  have he : A.center.ideal (A.nativeOpens i) = ⊥ := by rw [hzero]; rfl
  rw [A.center_ideal i] at he
  have hm := congrArg (Ideal.map (Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv (A.rings i) (A.map i)).toRingHom) he
  rw [Ideal.map_comap_of_surjective (Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv (A.rings i) (A.map i)).toRingHom
    (Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv (A.rings i) (A.map i)).surjective, Ideal.map_bot] at hm
  exact (A.choice i).center_ne_bot hm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent
