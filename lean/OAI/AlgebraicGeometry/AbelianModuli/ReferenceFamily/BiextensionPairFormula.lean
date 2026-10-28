import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.Biextension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PairClass

/-! # Biextension Pair Formula -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionPairFormula

noncomputable section

/-! Evaluating the original ample polarization formula at two
arbitrary test-scheme points gives the corresponding original Poincare
pairing formula. No restriction to reduced or field-valued tests is made. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem biextensionPair_tensor_formula {S : Scheme.{0}} (G : Over S) [GrpObj G]
    (L : HilbertConstruction.Line.Bundles.LineBundle G.left) (Q : HilbertConstruction.Line.Bundles.LineBundle (G ⊗ G).left)
    (e : ((Q.tensor (L.pullback (fst G G).left)).tensor (L.pullback (snd G G).left)).sheaf ≅
      (L.pullback (MonObj.mul (X := G)).left).sheaf)
    (T : Over S) (a b : T ⟶ G) :
    (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift a b).left (HilbertConstruction.Line.Bundles.LineBundle.classOf Q) *
      HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback a.left)) * HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback b.left) =
      HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (a * b).left) := by
  have h₁ : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift a b).left (HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (fst G G).left)) =
      HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback a.left) :=
    (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (lift a b).left (fst G G).left (HilbertConstruction.Line.Bundles.LineBundle.classOf L)).symm.trans
      (congrArg (fun f => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (HilbertConstruction.Line.Bundles.LineBundle.classOf L)) (congrArg Over.Hom.left (lift_fst a b)))
  have h₂ : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift a b).left (HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd G G).left)) =
      HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback b.left) :=
    (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (lift a b).left (snd G G).left (HilbertConstruction.Line.Bundles.LineBundle.classOf L)).symm.trans
      (congrArg (fun f => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (HilbertConstruction.Line.Bundles.LineBundle.classOf L)) (congrArg Over.Hom.left (lift_snd a b)))
  have hm : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift a b).left (HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (MonObj.mul (X := G)).left)) =
      HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (a * b).left) :=
    (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (lift a b).left (MonObj.mul (X := G)).left (HilbertConstruction.Line.Bundles.LineBundle.classOf L)).symm
  have he : (HilbertConstruction.Line.Bundles.LineBundle.classOf Q * HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (fst G G).left)) *
      HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd G G).left) = HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (MonObj.mul (X := G)).left) :=
    Quotient.sound ⟨e⟩
  have h := congrArg (HilbertConstruction.Line.Bundles.LineBundle.pullbackClassMonoidHom (lift a b).left) he
  rw [map_mul, map_mul] at h
  change (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift a b).left (HilbertConstruction.Line.Bundles.LineBundle.classOf Q) *
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift a b).left (HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (fst G G).left))) *
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift a b).left (HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd G G).left)) =
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift a b).left (HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (MonObj.mul (X := G)).left)) at h
  rw [h₁, h₂, hm] at h
  exact h

variable {g N : ℕ} {δ : Fin g → ℕ} (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)

theorem polarizationBiextension_pair_class (T : Over Foundations.Scheme.ProjectiveSpace.complexBase) (a b : T ⟶ A.abelian.scheme) :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift a b).left (HilbertConstruction.Line.Bundles.LineBundle.classOf (Polarization.Biextension.polarizationOriginalBiextension A)) =
      A.dual.poincarePairClass T (a ≫ A.polarization.isogeny.hom) b := by
  have h := congrArg (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift a b).left) (Polarization.Biextension.polarizationOriginalBiextension_class A)
  change _ = HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift a b).left
    (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.polarization.isogeny.hom ⊗ₘ 𝟙 A.abelian.scheme).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare)) at h
  have hj : lift a b ≫ (A.polarization.isogeny.hom ⊗ₘ 𝟙 A.abelian.scheme) =
      lift (a ≫ A.polarization.isogeny.hom) b := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have hp := (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (lift a b).left
    (A.polarization.isogeny.hom ⊗ₘ 𝟙 A.abelian.scheme).left (HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare)).symm
  have hd : A.dual.poincarePairClass T (a ≫ A.polarization.isogeny.hom) b =
      HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (a ≫ A.polarization.isogeny.hom) b).left
        (HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare) :=
    Quotient.sound ⟨A.dual.poincarePairDirectIso (a ≫ A.polarization.isogeny.hom) b⟩
  exact h.trans (hp.trans ((congrArg (fun f => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare))
    (congrArg Over.Hom.left hj)).trans hd.symm))

theorem polarizationPair_tensor_formula (T : Over Foundations.Scheme.ProjectiveSpace.complexBase) (a b : T ⟶ A.abelian.scheme) :
    (A.dual.poincarePairClass T (a ≫ A.polarization.isogeny.hom) b *
      HilbertConstruction.Line.Bundles.LineBundle.classOf ((Intrinsic.ChernPairing.polarizationLineBundle A).pullback a.left)) *
      HilbertConstruction.Line.Bundles.LineBundle.classOf ((Intrinsic.ChernPairing.polarizationLineBundle A).pullback b.left) =
      HilbertConstruction.Line.Bundles.LineBundle.classOf ((Intrinsic.ChernPairing.polarizationLineBundle A).pullback (a * b).left) := by
  have h := biextensionPair_tensor_formula A.abelian.scheme (Intrinsic.ChernPairing.polarizationLineBundle A)
    (Polarization.Biextension.polarizationOriginalBiextension A) (Polarization.Biextension.polarizationLineBundle_poincare A).some T a b
  rw [polarizationBiextension_pair_class] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionPairFormula
