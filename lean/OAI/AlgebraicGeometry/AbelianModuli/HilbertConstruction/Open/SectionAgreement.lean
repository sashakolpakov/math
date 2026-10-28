import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SheafOverlapEquivalence

/-! # Section Agreement -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.SectionAgreement

noncomputable section

/-! Agreement of sections is symmetric in the two opens and can be checked on an equal model of their intersection. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

universe u v

variable {R : Type u} [CommRing R] {X : TopCat.{u}}
variable (F : TopCat.Presheaf (ModuleCat.{u} R) X)

theorem openSectionPair_iff_of_open_eq {U V W : Opens X}
    (hU : W ≤ U) (hV : W ≤ V) (hW : W = U ⊓ V) (x : F.obj (op U)) (y : F.obj (op V)) :
    F.map (homOfLE hU).op x = F.map (homOfLE hV).op y ↔
      F.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op x =
        F.map (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op y := by
  subst W
  rfl

theorem openSectionPair_symm {U V : Opens X} {x : F.obj (op U)} {y : F.obj (op V)}
    (h : F.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op x =
      F.map (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op y) :
    F.map (homOfLE (show V ⊓ U ≤ V from inf_le_left)).op y =
      F.map (homOfLE (show V ⊓ U ≤ U from inf_le_right)).op x :=
  (openSectionPair_iff_of_open_eq F inf_le_right inf_le_left (inf_comm U V) y x).mp h.symm

theorem compatibleOpenSectionModule_iff_ordered {ι : Type v} [LinearOrder ι]
    (U : ι → Opens X) (x : (i : ι) → F.obj (op (U i))) :
    x ∈ Module.SheafOverlapEquivalence.compatibleOpenSectionModule F U ↔ ∀ i j, i < j →
      F.map (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op (x i) =
        F.map (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op (x j) := by
  constructor
  · intro h i j _
    exact h i j
  · intro h i j
    rcases lt_trichotomy i j with hij | hij | hji
    · exact h i j hij
    · subst j
      rfl
    · exact openSectionPair_symm F (h j i hji)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.SectionAgreement
