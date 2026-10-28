import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FramedHomComplex

/-! # Framed Hom Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FramedHomNaturality

noncomputable section

/-! The framed principal-open comparison commutes with the original
maps of sheaf resolutions. The square uses literal affine chart maps. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (N : X.Modules) [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(X, U)] Γ(X, U))
  {ι : Type*} (c : ComplexShape ι)

local instance sections_additive : (AffineOpen.InternalHom.sections U hU).Additive where
  map_add {_M _N} _f _g := rfl

def iso (K : HomologicalComplex X.Modules c) [∀ n, (K.X n).IsQuasicoherent] :=
  (FramedHomComplex.iso U hU N e c K) ≪≫
    FramedHomComplex.chartHomIso U hU c K

theorem naturality {K L : HomologicalComplex X.Modules c}
    [∀ n, (K.X n).IsQuasicoherent] [∀ n, (L.X n).IsQuasicoherent] (f : K ⟶ L) :
    ((InternalHomComplex.sectionHom U hU N).mapHomologicalComplex c.symm).map
        ((HomologicalComplex.opFunctor X.Modules c).map f.op) ≫ (iso U hU N e c K).hom =
      (iso U hU N e c L).hom ≫ HomCoefficientFunctor.map Γ(X, U)
        (LineFrame.scalars U hU)
        (((AffineOpen.InternalHom.sections U hU).mapHomologicalComplex c).map f) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  apply LinearMap.ext
  intro m
  change LineFrame.frame U hU N e r.unop
      (LiteralHomEquiv.equiv U hU r.unop.val (K.X i) N
        ((ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomFunctoriality.Construction.sheafHomMap (f.f i) (𝟙 N)).val.app (op (SectionPresheaf.openSubset U r.unop)) q)
        ((Affine.ChartSections.iso U hU (K.X i)).inv m)) =
    LineFrame.frame U hU N e r.unop
      (LiteralHomEquiv.equiv U hU r.unop.val (L.X i) N q
        ((Affine.ChartSections.iso U hU (L.X i)).inv
          ((AffineOpen.InternalHom.sections U hU).map (f.f i) m)))
  apply congrArg (LineFrame.frame U hU N e r.unop)
  rw [LiteralHomEquiv.precomp]
  apply congrArg (LiteralHomEquiv.equiv U hU r.unop.val (L.X i) N q)
  exact (ConcreteCategory.congr_hom
    ((AffineOpen.LinearHom.sectionsIso U hU).inv.naturality (f.f i)) m).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FramedHomNaturality
