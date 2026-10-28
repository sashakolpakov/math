import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.FixedBasis
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Groups

/-! # Fixed Label Congruence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The single ordered reference lattice basis identifies principal
congruence with equality of its actual full-level labels. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

theorem Datum.RankThreePELDatum.fixedLevelLabel_congruent (N : ℕ) (v w : P.lattice)
    (h : ∃ t : P.lattice, w - v = N • t) : P.fixedLevelLabel hP N w = P.fixedLevelLabel hP N v := by
  obtain ⟨t, ht⟩ := h
  funext i
  have he := congrArg (fun x : P.lattice => ((P.referenceBasis hP).repr x i : ZMod N)) ht
  change ((P.referenceBasis hP).repr w i : ZMod N) = ((P.referenceBasis hP).repr v i : ZMod N)
  apply sub_eq_zero.mp
  simpa [map_sub, map_nsmul, nsmul_eq_mul] using he

theorem Datum.RankThreePELDatum.fixedLevelLabel_principal (N : ℕ) (g : Groups.principalSpecialUnitary P.b P.lattice N) (v : P.lattice) :
    P.fixedLevelLabel hP N ⟨g.val v.val, (g.property.1.1 v.val).mp v.property⟩ = P.fixedLevelLabel hP N v := by
  apply P.fixedLevelLabel_congruent hP N
  obtain ⟨t, ht, he⟩ := g.property.1.2 v.val v.property
  exact ⟨⟨t, ht⟩, Subtype.ext he⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
