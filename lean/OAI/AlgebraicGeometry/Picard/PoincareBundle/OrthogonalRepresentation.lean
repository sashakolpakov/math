import OAI.AlgebraicGeometry.Picard.PoincareBundle.OrthogonalBaseChange
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.WeilCanonicalComparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ContainmentMap

/-! # Orthogonal Representation -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.OrthogonalRepresentation

noncomputable section

/-! The full torsion-point annihilator is the annihilator of the actual represented kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionTestPoints
attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {S : Scheme} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] (n : ℕ)
  (hker : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)

/-- Include a represented scalar-kernel point in the complete torsion-point functor. -/
def point {T : Over S} (y : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A) ^ n)) : TorsionTestPoints.Point A n T :=
  ⟨y ≫ Kernel.Scheme.kernelInclusion ((𝟙 A) ^ n), Field.WeilCanonicalComparison.kernel_torsion A n y⟩

/-- Restricting represented points restricts the same full scheme-valued point. -/
theorem point_restrict {T U : Over S} (a : U ⟶ T) (y : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A) ^ n)) :
    point n (a ≫ y) = TorsionTestPoints.restrict a (point n y) :=
  Subtype.ext (Category.assoc _ _ _)

/-- Kernel containment preserves every included test point. -/
theorem point_kernel {T : Over S} (x : T ⟶ Kernel.Scheme.kernelObject f) :
    point n (x ≫ Kernel.ContainmentMap.torsionMap f n hker) =
      (⟨x ≫ Kernel.Scheme.kernelInclusion f, hker T _ (Kernel.Scheme.kernelPointsEquiv f T x).property⟩ : TorsionTestPoints.Point A n T) :=
  Subtype.ext ((Category.assoc _ _ _).trans
    (congrArg (fun i => x ≫ i) (Kernel.ContainmentMap.torsionMap_inclusion f n hker)))

/-- A full point-annihilator equality is exactly the represented-kernel annihilator equality. -/
theorem represented
    (V : ∀ T : Over S, TorsionTestPoints.Point A n T → TorsionTestPoints.Point A n T → Γ(T.left, ⊤)ˣ)
    (h : OrthogonalBaseChange.SelfAnnihilating f n hker V)
    (T : Over S) (y : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A) ^ n)) :
    (∀ (U : Over S) (a : U ⟶ T) (x : U ⟶ Kernel.Scheme.kernelObject f),
      V U (point n (x ≫ Kernel.ContainmentMap.torsionMap f n hker)) (point n (a ≫ y)) = 1) ↔
      ∃ x : T ⟶ Kernel.Scheme.kernelObject f, x ≫ Kernel.ContainmentMap.torsionMap f n hker = y := by
  let j := Kernel.ContainmentMap.torsionMap f n hker
  let i := Kernel.Scheme.kernelInclusion ((𝟙 A) ^ n)
  constructor
  · intro hy
    have hf : (point n y).val ≫ f = 1 := by
      apply (h T (point n y)).mp
      intro U a x hx
      let xH := (Kernel.Scheme.kernelPointsEquiv f U).symm ⟨x, hx⟩
      have hxH : xH ≫ Kernel.Scheme.kernelInclusion f = x :=
        congrArg Subtype.val ((Kernel.Scheme.kernelPointsEquiv f U).apply_symm_apply ⟨x, hx⟩)
      let x0 : TorsionTestPoints.Point A n U := ⟨x, hker U x hx⟩
      have hp : point n (xH ≫ j) = x0 := Subtype.ext
        (((Category.assoc _ _ _).trans
          (congrArg (fun z => xH ≫ z) (Kernel.ContainmentMap.torsionMap_inclusion f n hker))).trans hxH)
      have he := congrArg₂ (V U) hp (point_restrict n a y)
      exact he.symm.trans (hy U a xH)
    let xH := (Kernel.Scheme.kernelPointsEquiv f T).symm ⟨(point n y).val, hf⟩
    refine ⟨xH, ?_⟩
    apply (cancel_mono i).mp
    exact ((Category.assoc _ _ _).trans
      (congrArg (fun z => xH ≫ z) (Kernel.ContainmentMap.torsionMap_inclusion f n hker))).trans
        (congrArg Subtype.val ((Kernel.Scheme.kernelPointsEquiv f T).apply_symm_apply ⟨(point n y).val, hf⟩))
  · rintro ⟨xH, hxH⟩
    have hi : (point n y).val = xH ≫ Kernel.Scheme.kernelInclusion f :=
      (congrArg (fun z => z ≫ i) hxH).symm.trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun z => xH ≫ z) (Kernel.ContainmentMap.torsionMap_inclusion f n hker)))
    have hf : (point n y).val ≫ f = 1 :=
      (congrArg (fun z => z ≫ f) hi).trans (Kernel.Scheme.kernelPointsEquiv f T xH).property
    have hy := (h T (point n y)).mpr hf
    intro U a x
    have he := congrArg₂ (V U) (point_kernel f n hker x) (point_restrict n a y)
    exact he.trans (hy U a (x ≫ Kernel.Scheme.kernelInclusion f) (Kernel.Scheme.kernelPointsEquiv f U x).property)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.OrthogonalRepresentation
