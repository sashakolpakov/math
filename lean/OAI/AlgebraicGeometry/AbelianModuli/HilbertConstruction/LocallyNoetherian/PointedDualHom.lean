import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonoidHomOpenLocality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseSquareIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.UniversalPointedHomomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.DualProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackMonoidIso

/-! # Pointed Dual Hom -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.PointedDualHom

noncomputable section

/-! Pointed maps on arbitrary base changes of the duals of polarized families over a locally Noetherian base preserve the group law. The proof reduces through a pulled-back affine base cover and actual complete base-square isomorphisms. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

theorem baseChangedPointedDualMap_isMonHom_of_locallyNoetherian
    {S : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (hδ : ∀ j, 0 < δ j) (T : Over S)
    (f : (A.pullback T.hom).dual.abelian.scheme ⟶ (B.pullback T.hom).dual.abelian.scheme)
    (hf : η[(A.pullback T.hom).dual.abelian.scheme] ≫ f = η[(B.pullback T.hom).dual.abelian.scheme]) :
    IsMonHom f := by
  let C := S.affineOpenCover.openCover
  apply MonoidHomOpenLocality.isMonHom_of_openCover f (C.pullback₁ T.hom)
  intro i
  change S.affineOpenCover.I₀ at i
  have : IsAffine (C.X i) := inferInstanceAs (IsAffine (Spec (S.affineOpenCover.X i)))
  have hi : IsOpenImmersion (C.f i) := C.map_prop i
  have hloc : IsLocallyNoetherian (C.X i) :=
    @isLocallyNoetherian_of_isOpenImmersion (C.X i) S (C.f i) hi inferInstance
  have : IsNoetherian (C.X i) :=
    { toIsLocallyNoetherian := hloc, toCompactSpace := inferInstance }
  have : IsNoetherianRing Γ(C.X i, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let p := pullback.fst T.hom (C.f i)
  let q := pullback.snd T.hom (C.f i)
  let a := Moduli.Isomorphisms.LevelPreservingIso.baseSquare A T.hom (C.f i) p q
    (pullback.condition (f := T.hom) (g := C.f i))
  let b := Moduli.Isomorphisms.LevelPreservingIso.baseSquare B T.hom (C.f i) p q
    (pullback.condition (f := T.hom) (g := C.f i))
  let fp := (Over.pullback p).map f
  have hfp : η[((A.pullback T.hom).pullback p).dual.abelian.scheme] ≫ fp =
      η[((B.pullback T.hom).pullback p).dual.abelian.scheme] :=
    (MappedMonoidHomEquations.mappedMonoidHom_one_iff (Over.pullback p) f).mpr (congrArg (Over.pullback p).map hf)
  let v := a.dual.inv ≫ fp ≫ b.dual.hom
  have hv : IsMonHom v := Relative.UniversalPointedHomomorphism.relativeUniversalPointedMap_isMonHom
    (A.pullback (C.f i)).dual.abelian (B.pullback (C.f i)).dual.abelian
    ((A.pullback (C.f i)).dualProjectivePresentation_of_noetherian_affine hδ)
    ((B.pullback (C.f i)).dualProjectivePresentation_of_noetherian_affine hδ) (Over.mk q) v
    (MonoidHomOpenLocality.pointedMap_conjugate a.dual b.dual fp hfp)
  have : IsMonHom a.dual.symm.hom := a.symm.dualGroup
  have : IsMonHom b.dual.symm.hom := b.symm.dualGroup
  exact (ParameterPullbackMonoidIso.monoidHom_conjugate_iff a.dual.symm b.dual.symm fp).mp hv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.PointedDualHom
