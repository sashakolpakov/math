import OAI.AlgebraicGeometry.Albanese.Construction.FiniteRefinements

/-! # Fiber Injective -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.FiberInjective

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

@[reassoc (attr := simp)]
theorem factorFiberMap_fiberι {D A B : Scheme.{u}}
    (a : D ⟶ A) (φ : A ⟶ B) (y : B) :
    FiniteRefinements.factorFiberMap a φ y ≫ φ.fiberι y = (a ≫ φ).fiberι y ≫ a := by
  exact pullback.lift_fst _ _ _

/-- Injectivity of the map on a fiber detects equality of source points in
that fiber. -/
theorem factor_injective_on_fiber {D A B : Scheme.{u}}
    (a : D ⟶ A) (φ : A ⟶ B) (y : B)
    (hinj : Function.Injective (FiniteRefinements.factorFiberMap a φ y))
    {x z : D} (hx : (a ≫ φ) x = y) (hz : (a ≫ φ) z = y) (h : a x = a z) : x = z := by
  let x' := ((a ≫ φ).fiberHomeo y).symm ⟨x, hx⟩
  let z' := ((a ≫ φ).fiberHomeo y).symm ⟨z, hz⟩
  have hxx : (a ≫ φ).fiberι y x' = x :=
    (a ≫ φ).fiberι_fiberHomeo_symm y ⟨x, hx⟩
  have hzz : (a ≫ φ).fiberι y z' = z :=
    (a ≫ φ).fiberι_fiberHomeo_symm y ⟨z, hz⟩
  have heq : FiniteRefinements.factorFiberMap a φ y x' = FiniteRefinements.factorFiberMap a φ y z' := by
    apply (φ.fiberι y).isEmbedding.injective
    change (FiniteRefinements.factorFiberMap a φ y ≫ φ.fiberι y) x' =
      (FiniteRefinements.factorFiberMap a φ y ≫ φ.fiberι y) z'
    rw [factorFiberMap_fiberι]
    simpa only [Scheme.Hom.comp_apply, hxx, hzz] using h
  exact hxx.symm.trans ((congrArg ((a ≫ φ).fiberι y) (hinj heq)).trans hzz)

/-- The underlying scheme point of the group identity. -/
def identitySchemePoint (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : B.toOver.left :=
  (1 : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ B.toOver).left (IsLocalRing.closedPoint ℂ)

/-- Injectivity on the fiber over the final identity forces injectivity on
all rational points of a group homomorphism, by testing its kernel. -/
theorem hom_point_injective_of_identity_fiber
    (C A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : C.toOver ⟶ A.toOver) (φ : A.toOver ⟶ B.toOver)
    [IsMonHom a] [IsMonHom φ]
    (hinj : Function.Injective (FiniteRefinements.factorFiberMap a.left φ.left (identitySchemePoint B))) :
    Function.Injective (fun p : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ C.toOver => p ≫ a) := by
  apply (injective_iff_map_eq_one (IsMonHom.monoidHom a (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))).mpr
  intro p hp
  change p ≫ a = 1 at hp
  have hmap : p ≫ a = (1 : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ C.toOver) ≫ a := by simpa using hp
  have hc : p ≫ a ≫ φ = 1 := by rw [← Category.assoc, hp]; simp
  have h1 : (1 : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ C.toOver) ≫ a ≫ φ = 1 := by simp
  have hx : (a.left ≫ φ.left) (p.left (IsLocalRing.closedPoint ℂ)) = identitySchemePoint B :=
    congrArg (fun q : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ B.toOver =>
      q.left (IsLocalRing.closedPoint ℂ)) hc
  have hz : (a.left ≫ φ.left) (identitySchemePoint C) = identitySchemePoint B :=
    congrArg (fun q : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ B.toOver =>
      q.left (IsLocalRing.closedPoint ℂ)) h1
  have hpoints : a.left (p.left (IsLocalRing.closedPoint ℂ)) = a.left (identitySchemePoint C) :=
    congrArg (fun q : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ A.toOver =>
      q.left (IsLocalRing.closedPoint ℂ)) hmap
  have heq := factor_injective_on_fiber a.left φ.left (identitySchemePoint B) hinj hx hz hpoints
  have : LocallyOfFiniteType C.toOver.hom :=
    inferInstanceAs (LocallyOfFiniteType C.variety.structureMap)
  ext1
  exact ext_of_apply_closedPoint_eq C.toOver.hom p.w
    (1 : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ C.toOver).w heq

end

end OAI.AlgebraicGeometry.Albanese.Construction.FiberInjective
