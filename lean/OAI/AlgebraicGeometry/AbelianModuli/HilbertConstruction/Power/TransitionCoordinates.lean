import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionTransitions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.PowerNumerators

/-! # Transition Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.TransitionCoordinates

noncomputable section

/-! In a line-bundle frame, degree transitions multiply coordinates by powers of the denominator. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {L : X.Modules}

/-- Multiplication by a section has its ordinary coordinate as coefficient
between the consecutive power frames. -/
theorem multiplyPowerBySection_frame (e s : Line.Bundles.structureModule X ⟶ L) [IsIso e] (n : ℕ) :
    TensorPower.Maps.tensorPowerSection e n ≫ Section.PowerMultiplication.multiplyPowerBySection s n =
      Frame.Coordinates.frameCoordinateEnd e s ≫ TensorPower.Maps.tensorPowerSection e (n + 1) := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro r
  change Γ(X, U) at r
  let a := Frame.Coordinates.frameCoordinateEnd e s
  let c : Γ(X, U) := a.app U (1 : Γ(X, U))
  have hs : s.app U (1 : Γ(X, U)) = c • e.app U (1 : Γ(X, U)) := by
    have h := congrArg (fun z : Line.Bundles.structureModule X ⟶ L => z.app U (1 : Γ(X, U)))
      (Frame.Coordinates.frameCoordinateEnd_frame e s)
    change e.app U c = s.app U (1 : Γ(X, U)) at h
    have he := e.app_smul c (1 : Γ(X, U))
    change e.app U (show Γ(X, U) from c * 1) = c • e.app U (1 : Γ(X, U)) at he
    rw [mul_one] at he
    exact h.symm.trans he
  have hc : Fin.cons (e.app U (1 : Γ(X, U))) (fun _ : Fin n => e.app U (1 : Γ(X, U))) =
      (fun _ : Fin (n + 1) => e.app U (1 : Γ(X, U))) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have hβ := congrArg (fun β : Tensor.Powers.SheafMultilinearMap L n (TensorPower.PowerSheaf.tensorPowerModule L (n + 1)) =>
    β.app U (fun _ => e.app U (1 : Γ(X, U)))) (Section.PowerMultiplication.multiplyPowerBySection_spec s n)
  change (Section.PowerMultiplication.multiplyPowerBySection s n).app U
      ((TensorPower.Maps.tensorPowerMultilinear L n).app U (fun _ => e.app U (1 : Γ(X, U)))) =
    (TensorPower.Maps.tensorPowerMultilinear L (n + 1)).app U
      (Fin.cons (s.app U (1 : Γ(X, U))) (fun _ => e.app U (1 : Γ(X, U)))) at hβ
  rw [hs, MultilinearMap.cons_smul, hc] at hβ
  change (Section.PowerMultiplication.multiplyPowerBySection s n).app U ((TensorPower.Maps.tensorPowerSection e n).app U r) =
    (TensorPower.Maps.tensorPowerSection e (n + 1)).app U (a.app U r)
  have hp := TensorPower.Maps.tensorPowerSection_app e n U r
  have hp' := TensorPower.Maps.tensorPowerSection_app e (n + 1) U (show Γ(X, U) from a.app U r)
  have har : (show Γ(X, U) from a.app U r) = r * c := TensorPower.Units.structureModuleEnd_app a U r
  exact (congrArg (fun z : Γ(TensorPower.PowerSheaf.tensorPowerModule L n, U) => (Section.PowerMultiplication.multiplyPowerBySection s n).app U z) hp).trans
    (((Section.PowerMultiplication.multiplyPowerBySection s n).app_smul r _).trans
      ((congrArg (fun z : Γ(TensorPower.PowerSheaf.tensorPowerModule L (n + 1), U) => r • z) hβ).trans
        ((smul_smul r c _).trans
          ((congrArg (fun z : Γ(X, U) => z •
            (TensorPower.Maps.tensorPowerMultilinear L (n + 1)).app U (fun _ => e.app U (1 : Γ(X, U)))) har).symm.trans
            hp'.symm))))

/-- Iterated degree transitions multiply the power frame by the corresponding
power of the coordinate endomorphism. -/
theorem powerSectionTransition_frame (e s : Line.Bundles.structureModule X ⟶ L) [IsIso e] (n m : ℕ) :
    TensorPower.Maps.tensorPowerSection e n ≫ SectionTransitions.powerSectionTransition s n m =
      ((Frame.Coordinates.frameCoordinateEnd e s) ^ m) ≫ TensorPower.Maps.tensorPowerSection e (n + m) := by
  induction m with
  | zero => simp only [SectionTransitions.powerSectionTransition, pow_zero, Nat.add_zero, Category.comp_id]; rfl
  | succ m ih =>
    change TensorPower.Maps.tensorPowerSection e n ≫ (SectionTransitions.powerSectionTransition s n m ≫ Section.PowerMultiplication.multiplyPowerBySection s (n + m)) = _
    rw [← Category.assoc, ih, Category.assoc, multiplyPowerBySection_frame, pow_succ']
    rfl

/-- On arbitrary numerators, the transition multiplies their frame coordinates
by the corresponding power of the denominator coordinate. -/
theorem frameCoordinate_powerSectionTransition_frame (e s : Line.Bundles.structureModule X ⟶ L)
    [IsIso e] (n m : ℕ) (t : Line.Bundles.structureModule X ⟶ TensorPower.PowerSheaf.tensorPowerModule L n) :
    Frame.Coordinates.frameCoordinate (TensorPower.Maps.tensorPowerSection e (n + m)) (t ≫ SectionTransitions.powerSectionTransition s n m) =
      Frame.Coordinates.frameCoordinate (TensorPower.Maps.tensorPowerSection e n) t * (Frame.Coordinates.frameCoordinate e s) ^ m := by
  let a : End (Line.Bundles.structureModule X) := Frame.Coordinates.frameCoordinateEnd e s
  let b : End (Line.Bundles.structureModule X) := Frame.Coordinates.frameCoordinateEnd (TensorPower.Maps.tensorPowerSection e n) t
  let z : End (Line.Bundles.structureModule X) := b ≫ (a ^ m)
  have ht : t ≫ SectionTransitions.powerSectionTransition s n m = z ≫ TensorPower.Maps.tensorPowerSection e (n + m) := by
    rw [← Frame.Coordinates.frameCoordinateEnd_frame (TensorPower.Maps.tensorPowerSection e n) t, Category.assoc,
      powerSectionTransition_frame]
    rfl
  have hz : Frame.Coordinates.structureModuleEndValue X z =
      Frame.Coordinates.frameCoordinate (TensorPower.Maps.tensorPowerSection e n) t * (Frame.Coordinates.frameCoordinate e s) ^ m := by
    change Frame.Coordinates.structureModuleEndValue X (a ^ m * b) = _
    rw [map_mul, map_pow, mul_comm]
    rfl
  exact (congrArg (fun z : Line.Bundles.structureModule X ⟶ TensorPower.PowerSheaf.tensorPowerModule L (n + m) =>
    Frame.Coordinates.frameCoordinate (TensorPower.Maps.tensorPowerSection e (n + m)) z) ht).trans
    ((Framed.AffineExtension.frameCoordinate_scalar_frame (TensorPower.Maps.tensorPowerSection e (n + m)) z).trans hz)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.TransitionCoordinates
