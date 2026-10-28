import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RationalCoefficient
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Rational Section Gluing -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-! # LineBundleCycles: actual local representatives of a rational line-bundle section glue uniquely -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X : Scheme.{0}} [IsIntegral X] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.localSections_agree_on_overlap (x y : X) (U V : X.Opens) [Nonempty U] [Nonempty V]
    (hU : U ≤ L.trivializingOpen x) (hV : V ≤ L.trivializingOpen y)
    (s : Γ(L.sheaf, U)) (t : Γ(L.sheaf, V))
    (hst : L.localRationalCoefficient x U hU s = L.localRationalCoefficient y V hV t) :
    L.sheaf.presheaf.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op s =
      L.sheaf.presheaf.map (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op t := by
  classical
  let W : X.Opens := U ⊓ V
  by_cases hW : Nonempty W
  · let : Nonempty W := hW
    apply L.localRationalCoefficient_injective x W (inf_le_left.trans hU)
    rw [L.localRationalCoefficient_restrict x inf_le_left hU,
      L.localRationalCoefficient_frame x y (U ⊓ V) (inf_le_left.trans hU) (inf_le_right.trans hV),
      L.localRationalCoefficient_restrict y inf_le_right hV]
    exact hst
  · apply L.sheaf.isSheaf.section_ext
    intro z hz
    exact (hW ⟨⟨z, hz⟩⟩).elim

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.localRationalSections_compatible {ι : Type} (x : ι → X) (U : ι → X.Opens)
    [∀ i, Nonempty (U i)] (hU : ∀ i, U i ≤ L.trivializingOpen (x i))
    (s : ∀ i, Γ(L.sheaf, U i)) (a : X.functionField)
    (hs : ∀ i, L.localRationalCoefficient (x i) (U i) (hU i) (s i) = a) :
    TopCat.Presheaf.IsCompatible L.sheaf.presheaf U s := by
  intro i j
  exact L.localSections_agree_on_overlap (x i) (x j) (U i) (U j) (hU i) (hU j)
    (s i) (s j) ((hs i).trans (hs j).symm)

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.existsUnique_gluedRationalSection {ι : Type} (x : ι → X) (U : ι → X.Opens)
    [∀ i, Nonempty (U i)] (hU : ∀ i, U i ≤ L.trivializingOpen (x i))
    (s : ∀ i, Γ(L.sheaf, U i)) (a : X.functionField)
    (hs : ∀ i, L.localRationalCoefficient (x i) (U i) (hU i) (s i) = a) :
    ∃! t : Γ(L.sheaf, iSup U), ∀ i,
      L.sheaf.presheaf.map (homOfLE (le_iSup U i)).op t = s i := by
  let F : TopCat.Sheaf Ab.{0} X := ⟨L.sheaf.presheaf, L.sheaf.isSheaf⟩
  exact F.existsUnique_gluing U s (L.localRationalSections_compatible x U hU s a hs)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
