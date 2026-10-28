import OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Functor
import OAI.NumberTheory.PadicHodge.IntegralComparison.FlatFromNonemptyLimits

/-! # Limits -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Limits

noncomputable section

/-!
# IntegralComparison: flatness of principal opens in a crystalline slice

The principal-open inclusion preserves binary products and equalizers.
Products lift because both functions become units; equalizers are
identities in the principal-open category. The unit open supplies a
nonempty incoming category for every slice object.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalizationLift
open OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalOpens.Category (Principal)
open OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Functor

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} (U : BigCrystallineSite.Object p B J δ f)

def lift {r s : PrincipalOpens.Category.Principal U.ring} (T : Over U) (a : T ⟶ Functor.object U r) (b : T ⟶ Functor.object U s) :
    T ⟶ Functor.object U (PrincipalOpens.Category.product U.ring r s) :=
  Over.homMk (Crystalline.LocalizationLift.liftHom T.hom (r.function * s.function) (by
    change IsUnit (T.hom.ringMap.toRingHom (r.function * s.function))
    rw [map_mul]
    exact (Functor.unit_of_factor U T.hom r.function a.left (Over.w a)).mul
      (Functor.unit_of_factor U T.hom s.function b.left (Over.w b))))
    (Crystalline.LocalizationLift.liftHom_comp T.hom (r.function * s.function) _)

def imageFan (r s : PrincipalOpens.Category.Principal U.ring) : BinaryFan (Functor.object U r) (Functor.object U s) :=
  BinaryFan.mk ((Functor.inclusion U).map (PrincipalOpens.Category.fst U.ring r s))
    ((Functor.inclusion U).map (PrincipalOpens.Category.snd U.ring r s))

def isImageProduct (r s : PrincipalOpens.Category.Principal U.ring) : IsLimit (imageFan U r s) :=
  BinaryFan.isLimitMk (fun c => lift U c.pt c.fst c.snd)
    (fun _ => Functor.hom_ext U _ _) (fun _ => Functor.hom_ext U _ _)
    (fun _ _ _ _ => Functor.hom_ext U _ _)

instance inclusion_preserves_pair (r s : PrincipalOpens.Category.Principal U.ring) : PreservesLimit (pair r s) (Functor.inclusion U) := by
  apply preservesLimit_of_preserves_limit_cone (PrincipalOpens.Category.isProduct U.ring r s)
  exact (isLimitMapConeBinaryFanEquiv (Functor.inclusion U)
    (PrincipalOpens.Category.fst U.ring r s) (PrincipalOpens.Category.snd U.ring r s)).symm
      (isImageProduct U r s)

instance inclusion_preservesBinaryProducts : PreservesLimitsOfShape (Discrete WalkingPair) (Functor.inclusion U) where
  preservesLimit {K} := by
    have := inclusion_preserves_pair U (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)
    exact preservesLimit_of_iso_diagram _ (diagramIsoPair K).symm

instance inclusion_preserves_equalizer {r s : PrincipalOpens.Category.Principal U.ring} (a b : r ⟶ s) :
    PreservesLimit (parallelPair a b) (Functor.inclusion U) := by
  have he : a = b := Subsingleton.elim _ _
  apply preservesLimit_of_preserves_limit_cone (isLimitIdFork he)
  refine (isLimitMapConeForkEquiv (Functor.inclusion U) (show (𝟙 r) ≫ a = (𝟙 r) ≫ b by rw [he])).symm ?_
  refine Fork.IsLimit.mk _ (fun c => c.ι) ?_ ?_
  · intro c
    exact Functor.hom_ext U _ _
  · intro c m hm
    exact Functor.hom_ext U _ _

instance inclusion_preservesEqualizers : PreservesLimitsOfShape WalkingParallelPair (Functor.inclusion U) where
  preservesLimit {K} := by
    have := inclusion_preserves_equalizer U (K.map WalkingParallelPairHom.left)
      (K.map WalkingParallelPairHom.right)
    exact preservesLimit_of_iso_diagram _ (diagramIsoParallelPair K).symm

theorem incoming_nonempty (T : Over U) : Nonempty (StructuredArrow T (Functor.inclusion U)) :=
  ⟨StructuredArrow.mk (Functor.toTerminal U T)⟩

/-- Extension from principal opens has the finite-limit flatness needed for Ext comparison. -/
instance inclusion_flat : RepresentablyFlat (Functor.inclusion U) :=
  FlatFromNonemptyLimits.flat (Functor.inclusion U) (incoming_nonempty U)

instance inclusion_final : (Functor.inclusion U).Final := final_of_representablyFlat _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Limits
