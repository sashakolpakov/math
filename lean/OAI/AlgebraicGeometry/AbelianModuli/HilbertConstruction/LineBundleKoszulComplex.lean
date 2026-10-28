import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.KoszulTermIsomorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionKoszulCoherent

/-! # Line Bundle Koszul Complex -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundleKoszulComplex

noncomputable section

/-! The actual Koszul complex of sections belonging to different line
bundles. Its terms are coherent, its degrees lie in the expected finite
interval, and it contracts after a pullback where any chosen section
is a frame. This permits one hyperplane cut and several cuts by powers. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

abbrev LineBundleSection (X : Scheme.{u}) :=
  Σ L : Line.Bundles.LineBundle X, Line.Bundles.structureModule X ⟶ L.sheaf

local instance mixedKoszulPullbackAdditive {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (Scheme.Modules.pullback f)
  exact Functor.additive_of_preservesBinaryBiproducts _

def mixedLineBundleKoszulComplex {X : Scheme.{u}} (M : X.Modules) :
    List (LineBundleSection X) → CochainComplex X.Modules ℤ
  | [] => (HomologicalComplex.single X.Modules (.up ℤ) 0).obj M
  | b :: bs => LineBundle.SectionKoszulStep.lineBundleSectionKoszulStep b.1 b.2 (mixedLineBundleKoszulComplex M bs)

theorem mixedLineBundleKoszulComplex_isZero_X {X : Scheme.{u}}
    (M : X.Modules) (bs : List (LineBundleSection X)) (i : ℤ)
    (hi : i < -(bs.length : ℤ) ∨ 0 < i) :
    IsZero ((LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs).X i) := by
  induction bs generalizing i with
  | nil =>
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i
      (by simp only [List.length_nil, Nat.cast_zero, neg_zero] at hi; omega)
  | cons b bs ih =>
    apply (LineBundle.SectionKoszulStep.lineBundleSectionKoszulStep_isZero_X_iff b.1 b.2 _ i).mpr
    constructor
    · apply ih
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hi
      omega
    · exact Functor.map_isZero (LineBundle.TensorEquivalence.lineBundleTensorEquivalence b.1).functor
        (ih i (by simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hi; omega))

theorem mixedLineBundleKoszulComplex_pullback_contractible
    {X Y : Scheme.{u}} (M : X.Modules) (bs : List (LineBundleSection X)) (f : Y ⟶ X)
    (hs : ∃ b ∈ bs, IsIso ((Scheme.Modules.pullback f).map b.2)) :
    Nonempty (Homotopy (𝟙 (((Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ)).obj
      (LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs))) 0) := by
  induction bs with
  | nil => simp at hs
  | cons b bs ih =>
    obtain ⟨a, ha, hiso⟩ := hs
    rcases List.mem_cons.mp ha with rfl | ha
    · have := hiso
      exact ⟨LineBundle.SectionKoszulStep.lineBundleSectionKoszulStep_pullback_contractible a.1 a.2 f
        (LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs)⟩
    · exact LineBundle.SectionKoszulComplex.lineBundleSectionKoszulStep_pullback_contractible_of_tail b.1 b.2 f
        (LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs) (ih ⟨a, ha, hiso⟩)

theorem mixedLineBundleKoszulComplex_coherent {X : Scheme.{u}}
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (bs : List (LineBundleSection X)) (i : ℤ) :
    ((LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs).X i).IsQuasicoherent ∧
      ((LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs).X i).IsFiniteType := by
  induction bs generalizing i with
  | nil =>
    by_cases hi : i = 0
    · subst i
      simpa only [LineBundleKoszulComplex.mixedLineBundleKoszulComplex, HomologicalComplex.single_obj_X_self] using
        (show M.IsQuasicoherent ∧ M.IsFiniteType from ⟨inferInstance, inferInstance⟩)
    · exact ZeroModuleCoherence.module_coherent_of_isZero _
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi)
  | cons b bs ih =>
    let C := LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs
    let F := (LineBundle.TensorEquivalence.lineBundleTensorEquivalence b.1).functor
    have hnext := ih (i + 1)
    have hhere := ih i
    have : (C.X (i + 1)).IsQuasicoherent := hnext.1
    have : (C.X (i + 1)).IsFiniteType := hnext.2
    have : (C.X i).IsQuasicoherent := hhere.1
    have : (C.X i).IsFiniteType := hhere.2
    have : (F.obj (C.X i)).IsQuasicoherent := LeftTensorCoherence.lineBundleTensorLeft_quasicoherent b.1 _
    have : (F.obj (C.X i)).IsFiniteType := LeftTensorCoherence.lineBundleTensorLeft_finiteType b.1 _
    have hq := Coherent.BinaryBiproduct.module_biprod_quasicoherent (C.X (i + 1)) (F.obj (C.X i))
    have := Coherent.BinaryBiproduct.module_biprod_finiteType (C.X (i + 1)) (F.obj (C.X i))
    let e := LineBundle.KoszulTermIsomorphisms.lineBundleSectionKoszulStep_XIsoBiprod b.1 b.2 C i
    have hsource : ((LineBundleKoszulComplex.mixedLineBundleKoszulComplex M (b :: bs)).X i).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm hq
    exact ⟨hsource, Quasicoherent.RestrictionFiniteType.quasicoherent_finiteType_of_iso e.symm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundleKoszulComplex
