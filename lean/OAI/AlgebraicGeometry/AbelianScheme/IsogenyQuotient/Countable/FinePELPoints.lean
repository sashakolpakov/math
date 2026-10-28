import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.PELModel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FinePELPolarization
import Mathlib.Algebra.CharP.Algebra

/-! # Fine PEL Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.FinePELPoints.Construction

noncomputable section

/-! Every geometric point of the original unrestricted fine PEL
scheme factors through an actual countable field-valued point.
Fine classification proves equality of the original scheme maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
theorem finePEL_geometric_point_has_countable_model
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s N : ℕ} [NeZero N]
    {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K} (Z : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hZ : Z.IsFine)
    (k : Type) [Field k] [IsAlgClosed k] (j : K →+* k)
    (x : Over.mk (Spec.map (CommRingCat.ofHom j)) ⟶ Z.space) :
    ∃ (F : Subfield k) (jF : K →+* F), Countable F ∧ IsAlgClosed F ∧ F.subtype.comp jF = j ∧
      ∃ b : Over.mk (Spec.map (CommRingCat.ofHom jF)) ⟶ Z.space,
        Spec.map (CommRingCat.ofHom F.subtype) ≫ b.left = x.left := by
  have : CharZero k := charZero_of_injective_ringHom j.injective
  obtain ⟨F, jF, hF, hFa, hjF, B, q, hq, ⟨e⟩⟩ :=
    PELModel.Construction.countable_full_PEL_model_exists P iota j (Z.universal.pullback x)
  let b := FinePELTarget.Construction.finePELClassifyingMap Z hZ B
  have hb : q ≫ b = x := by
    calc
      q ≫ b = FinePELTarget.Construction.finePELClassifyingMap Z hZ (B.pullback q) :=
        (FinePELPolarization.Construction.finePELClassifyingMap_pullback Z hZ B q).symm
      _ = FinePELTarget.Construction.finePELClassifyingMap Z hZ (Z.universal.pullback x) :=
        (FinePELPolarization.Construction.finePELClassifyingMap_eq_of_iso Z hZ e.toPELIso).symm
      _ = x := (FinePELTarget.Construction.finePELClassifyingMap_unique Z hZ (Z.universal.pullback x) x
        ⟨AbelianModuli.ReferenceFamily.Models.PELPullbackIso.canonical Z.universal x⟩).symm
  exact ⟨F, jF, hF, hFa, hjF, b,
    (congrArg (fun f => f ≫ b.left) hq).symm.trans (congrArg Over.Hom.left hb)⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.FinePELPoints.Construction
