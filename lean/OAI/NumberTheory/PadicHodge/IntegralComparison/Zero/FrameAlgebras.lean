import OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.LevelFrame

/-! # Frame Algebras -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.FrameAlgebras

noncomputable section

/-!
# IntegralComparison: residue-field algebra maps attached to original zero-frame morphisms
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u

variable (p : ℕ) [Fact p.Prime] (k C : Type u) [Field k] [CharP k p]
  [CommRing C] [Algebra k C]
  (U : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)))
  (β : U ⟶ ZeroLevel.LevelFrame.frame p k C)

@[instance_reducible]
def ambientAlgebra : Algebra k U.ring :=
  (β.ringMap.toRingHom.comp (algebraMap k C)).toAlgebra

def chartMap : letI := ambientAlgebra p k C U β
    C →ₐ[k] U.ring := by
  letI := ambientAlgebra p k C U β
  exact { β.ringMap.toRingHom with commutes' := fun _ => rfl }

theorem coefficient_base (w : WittVector p k) :
    β.ringMap (algebraMap k C (WittVector.constantCoeff w)) = U.base w :=
  RingHom.congr_fun β.overBase w

variable (V : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)))
  (ζ : V ⟶ ZeroLevel.LevelFrame.frame p k C) (α : V ⟶ U)

theorem coefficients_agree (a : k) :
    α.ringMap (β.ringMap (algebraMap k C a)) = ζ.ringMap (algebraMap k C a) := by
  obtain ⟨w, rfl⟩ := WittVector.constantCoeff_surjective p a
  rw [coefficient_base, coefficient_base]
  exact RingHom.congr_fun α.overBase w

def map : letI := ambientAlgebra p k C U β
    letI := ambientAlgebra p k C V ζ
    U.ring →ₐ[k] V.ring := by
  letI := ambientAlgebra p k C U β
  letI := ambientAlgebra p k C V ζ
  exact { α.ringMap.toRingHom with commutes' := coefficients_agree p k C U β V ζ α }

theorem chart_reduction (c : C) :
    Ideal.Quotient.mk U.ideal (β.ringMap c) = BigCrystallineCover.closedRingMap p k C U c := by
  have hs := β.overX
  change Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap U (ZeroLevel.LevelFrame.frame p k C) β.ringMap)) ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal C))) = U.mapToX at hs
  rw [← Spec.map_comp, ← BigCrystallineCover.closedRingMap_spec p k C U] at hs
  have he := congrArg CommRingCat.Hom.hom (Spec.map_injective hs)
  exact RingHom.congr_fun he c

theorem closed_agreement (c : C) :
    ζ.ringMap c - α.ringMap (β.ringMap c) ∈ V.ideal := by
  apply Ideal.Quotient.eq.mp
  rw [chart_reduction p k C V ζ c]
  have hs := α.overX
  rw [← BigCrystallineCover.closedRingMap_spec p k C U,
    ← BigCrystallineCover.closedRingMap_spec p k C V] at hs
  change Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap V U α.ringMap)) ≫
    Spec.map (CommRingCat.ofHom (BigCrystallineCover.closedRingMap p k C U)) =
      Spec.map (CommRingCat.ofHom (BigCrystallineCover.closedRingMap p k C V)) at hs
  rw [← Spec.map_comp] at hs
  have he := congrArg CommRingCat.Hom.hom (Spec.map_injective hs)
  have hc := RingHom.congr_fun he c
  change BigCrystallineSite.Object.quotientMap V U α.ringMap (BigCrystallineCover.closedRingMap p k C U c) =
    BigCrystallineCover.closedRingMap p k C V c at hc
  rw [← chart_reduction p k C U β c] at hc
  exact hc.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.FrameAlgebras
