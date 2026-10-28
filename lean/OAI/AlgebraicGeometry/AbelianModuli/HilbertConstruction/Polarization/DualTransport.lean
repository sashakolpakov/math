import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.TargetTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.FiberComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorBaseChange

/-! # Dual Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Replacing a dual by a group-isomorphic dual with the same Poincare
class preserves the original geometric positivity and polarization type. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S T : Scheme.{u}} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
variable {D E : Dual.Data.DualAbelianData A} (e : D.abelian.scheme ≅ E.abelian.scheme) [IsMonHom e.hom]

omit [IsMonHom e.hom] in
theorem Polarization.DualTransport.polarizationBiextensionMap_dualTransport (p : A.scheme ⟶ D.abelian.scheme) (f : T ⟶ S) :
    Polarization.FiberComparison.polarizationBiextensionMap E (p ≫ e.hom) f =
      Polarization.FiberComparison.polarizationBiextensionMap D p f ≫ (e.hom ⊗ₘ 𝟙 A.scheme).left := by
  apply Over.tensorObj_ext
  · have h₁ := Polarization.FiberComparison.polarizationBiextensionMap_fst E (p ≫ e.hom) f
    have h₂ := Polarization.FiberComparison.polarizationBiextensionMap_fst D p f
    have ht : (e.hom ⊗ₘ 𝟙 A.scheme).left ≫ pullback.fst E.abelian.scheme.hom A.scheme.hom =
        pullback.fst D.abelian.scheme.hom A.scheme.hom ≫ e.hom.left :=
      Over.tensorHom_left_fst _ _ _ _
    exact h₁.trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ e.hom.left) h₂).symm.trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z => Polarization.FiberComparison.polarizationBiextensionMap D p f ≫ z) ht).symm.trans
            (Category.assoc _ _ _).symm))))
  · have ht : (e.hom ⊗ₘ 𝟙 A.scheme).left ≫ pullback.snd E.abelian.scheme.hom A.scheme.hom =
        pullback.snd D.abelian.scheme.hom A.scheme.hom :=
      (Over.tensorHom_left_snd _ _ _ _).trans (Category.comp_id _)
    exact (Polarization.FiberComparison.polarizationBiextensionMap_snd E (p ≫ e.hom) f).trans
      ((Polarization.FiberComparison.polarizationBiextensionMap_snd D p f).symm.trans
        ((congrArg (fun z => Polarization.FiberComparison.polarizationBiextensionMap D p f ≫ z) ht).symm.trans
          (Category.assoc _ _ _).symm))

variable (he : Line.Bundles.LineBundle.pullbackClass (e.hom ⊗ₘ 𝟙 A.scheme).left (Line.Bundles.LineBundle.classOf E.poincare) =
  Line.Bundles.LineBundle.classOf D.poincare)

def Polarization.DualTransport.polarizationBiextensionDualIso (p : A.scheme ⟶ D.abelian.scheme) (f : T ⟶ S) :
    (PolarizationData.polarizationBiextensionAt E (p ≫ e.hom) f).sheaf ≅ (PolarizationData.polarizationBiextensionAt D p f).sheaf :=
  (Scheme.Modules.pullbackCongr (Polarization.DualTransport.polarizationBiextensionMap_dualTransport e p f)).app E.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackComp (Polarization.FiberComparison.polarizationBiextensionMap D p f)
      (e.hom ⊗ₘ 𝟙 A.scheme).left).symm.app E.poincare.sheaf ≪≫
    (Scheme.Modules.pullback (Polarization.FiberComparison.polarizationBiextensionMap D p f)).mapIso (Quotient.exact he).some

include he in
omit [IsMonHom e.hom] in
theorem Polarization.DualTransport.positiveOnGeometricFiber_dualTransport (p : A.scheme ⟶ D.abelian.scheme)
    (K : Type u) [Field K] [IsAlgClosed K] (f : Spec (.of K) ⟶ S)
    (hp : PolarizationData.PositiveOnGeometricFiber D p K f) : PolarizationData.PositiveOnGeometricFiber E (p ≫ e.hom) K f := by
  obtain ⟨L, hL, hzero, ⟨hformula⟩⟩ := hp
  refine ⟨L, hL, hzero, ⟨?_⟩⟩
  exact Tensor.Bifunctor.tensorModuleMapIso
    (Tensor.Bifunctor.tensorModuleMapIso (Polarization.DualTransport.polarizationBiextensionDualIso e he p f) (Iso.refl _))
      (Iso.refl _) ≪≫ hformula

def PolarizationData.Polarization.dualTransport {δ : Fin g → ℕ} (p : PolarizationData.Polarization D δ) : PolarizationData.Polarization E δ where
  isogeny := p.isogeny.targetTransport e
  kernelType := p.kernelType.targetTransport e
  positive K _ _ f := Polarization.DualTransport.positiveOnGeometricFiber_dualTransport e he p.isogeny.hom K f (p.positive K f)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
