import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.GlobalSplittingCharacters
import OAI.RepresentationTheory.Theta.Adelic.ConstructNormalizedSplittings
import OAI.RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta

/-! # Intrinsic Unitary Splitting -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicUnitarySplitting.CM

noncomputable section

/-! ThetaCycle: construct the complete native local unitary splitting package
for the actual trace additive character, including unramified vacuum
normalization. Its actual finite action fixes each prescribed finite
Schwartz family on a compact open level. -/

open scoped _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta

variable (F : Type) [Field F] [NumberField F]
  (d : F) (hd : d ≠ 0) (hns : ¬ IsSquare d) (n m : ℕ) (hnm : 0 < n * m)
  (H : (Matrix (Fin n) (Fin n) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
  (W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
  (hH : H.val.conjTranspose = H.val) (hW : W.val.conjTranspose = -W.val)
  (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d n m H W)

def fieldUnitarySplittings :
    RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d n m H W hd (GlobalSplittingCharacters.CM.fieldGlobalSplittingCharacters F d hd hns n m) P :=
  Classical.choice (RepresentationTheory.Theta.Adelic.ConstructNormalizedSplittings.exists_normalized_local_splittings
    F d hd hns n m hnm H W hH hW (GlobalSplittingCharacters.CM.fieldGlobalSplittingCharacters F d hd hns n m) P)

theorem field_unitary_finite_theta_level
    (Φ : Finset (RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (n * m))) (K₀ : OpenSubgroup (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H)) :
    ∃ L : OpenSubgroup (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H), IsCompact (L : Set (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H)) ∧ L ≤ K₀ ∧
      ∀ f ∈ Φ, ∀ g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H.val, RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU F H g ∈ L →
        ∀ φ : RepresentationTheory.Theta.Adelic.ThetaEvaluation.ArchimedeanTests F (n * m),
          RepresentationTheory.Theta.Adelic.ThetaEvaluation.theta F (n * m)
            (RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta.archimedeanAction F H W hd (GlobalSplittingCharacters.CM.fieldGlobalSplittingCharacters F d hd hns n m) P
              (fieldUnitarySplittings F d hd hns n m hnm H W hH hW P)
              (RepresentationTheory.Theta.Adelic.RationalSU.rationalArchimedeanSU F H g) φ) f = RepresentationTheory.Theta.Adelic.ThetaEvaluation.theta F (n * m) φ f :=
  RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta.finite_family_theta_level F H W hd (GlobalSplittingCharacters.CM.fieldGlobalSplittingCharacters F d hd hns n m) P
    (fieldUnitarySplittings F d hd hns n m hnm H W hH hW P) hns hH hW hnm Φ K₀

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicUnitarySplitting.CM
