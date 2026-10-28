import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonoidHomOpenLocality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseSquareIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.UniversalPointedHomomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.NoetherianAffineProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackMonoidIso

/-! # Pointed Hom -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.PointedHom

noncomputable section

/-! Pointed maps on arbitrary base changes of polarized families over a locally Noetherian base preserve the group law. The proof reduces through a pulled-back affine base cover and actual complete base-square isomorphisms. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

theorem baseChangedPointedAbelianMap_isMonHom_of_locallyNoetherian
    {S : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (T : Over S)
    (f : (A.pullback T.hom).abelian.scheme ⟶ (B.pullback T.hom).abelian.scheme)
    (hf : η[(A.pullback T.hom).abelian.scheme] ≫ f = η[(B.pullback T.hom).abelian.scheme]) :
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
  have hfp : η[((A.pullback T.hom).pullback p).abelian.scheme] ≫ fp =
      η[((B.pullback T.hom).pullback p).abelian.scheme] :=
    (MappedMonoidHomEquations.mappedMonoidHom_one_iff (Over.pullback p) f).mpr (congrArg (Over.pullback p).map hf)
  let v := a.abelian.inv ≫ fp ≫ b.abelian.hom
  have hv : IsMonHom v := Relative.UniversalPointedHomomorphism.relativeUniversalPointedMap_isMonHom
    (A.pullback (C.f i)).abelian (B.pullback (C.f i)).abelian
    (A.pullback (C.f i)).projectivePresentation_of_noetherian_affine
    (B.pullback (C.f i)).projectivePresentation_of_noetherian_affine (Over.mk q) v
    (MonoidHomOpenLocality.pointedMap_conjugate a.abelian b.abelian fp hfp)
  have : IsMonHom a.abelian.symm.hom := a.symm.abelianGroup
  have : IsMonHom b.abelian.symm.hom := b.symm.abelianGroup
  exact (ParameterPullbackMonoidIso.monoidHom_conjugate_iff a.abelian.symm b.abelian.symm fp).mp hv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.PointedHom
