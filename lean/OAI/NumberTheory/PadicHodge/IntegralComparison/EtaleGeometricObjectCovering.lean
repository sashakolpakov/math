import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.Point
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty

/-! # Etale Geometric Object Covering -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleGeometricObjectCovering.Pro

noncomputable section

/-! A geometric-point object has only maximal covering sieves in any original small pro-étale site. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (K : Type u) [Field K] [IsAlgClosed K] (X : Scheme.{u})
  (g : Spec (CommRingCat.of K) ⟶ X) [WeaklyEtale g]

theorem split (S : Sieve (Scheme.ProEt.mk g)) (hS : S ∈ Scheme.ProEt.topology X _) : S = ⊤ := by
  have : (Scheme.ProEt.precoverage X).IsStableUnderComposition := by
    unfold Scheme.ProEt.precoverage
    infer_instance
  have : (Scheme.ProEt.precoverage X).IsStableUnderBaseChange := by
    unfold Scheme.ProEt.precoverage
    infer_instance
  have : (Scheme.ProEt.precoverage X).HasIsos := by
    unfold Scheme.ProEt.precoverage
    infer_instance
  obtain ⟨R, hR, hRS⟩ := Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hS
  have hR' : R.map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
      Scheme.precoverage @WeaklyEtale ((Scheme.ProEt.forget X ⋙ Over.forget X).obj (Scheme.ProEt.mk g)) := hR.2
  have hsurj := hR'.1
  rw [Scheme.jointlySurjectivePrecoverage, Presieve.mem_comap_jointlySurjectivePrecoverage_iff] at hsurj
  obtain ⟨Y, a, ha, y, _⟩ := hsurj (IsLocalRing.closedPoint K)
  have haweak : WeaklyEtale a := hR'.2 ha
  obtain @⟨U, a, hU⟩ := ha
  obtain ⟨s, hs⟩ := @OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.Point.Construction.weaklyEtale_exists_section K inferInstance inferInstance
    U.left a.left haweak y
  have hover : s ≫ U.hom = g := by
    have hw : a.left ≫ g = U.hom := MorphismProperty.Over.w a
    exact (congrArg (fun q : U.left ⟶ X => s ≫ q) hw.symm).trans
      ((Category.assoc s a.left g).symm.trans
        ((congrArg (fun q : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) => q ≫ g) hs).trans
          (Category.id_comp g)))
  let t : Scheme.ProEt.mk g ⟶ U := MorphismProperty.Over.homMk s hover
  have ht : t ≫ a = 𝟙 _ := by
    apply MorphismProperty.Over.Hom.ext
    exact hs
  exact Sieve.id_mem_iff_eq_top.mp (ht ▸ S.downward_closed (hRS _ _ hU) t)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleGeometricObjectCovering.Pro
