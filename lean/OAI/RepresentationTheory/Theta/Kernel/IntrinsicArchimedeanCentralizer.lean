import OAI.RepresentationTheory.Theta.Kernel.IntrinsicUniqueLiftCentralizer
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicArchimedeanIndependence
import OAI.RepresentationTheory.Theta.Adelic.IntrinsicCoverTopology

/-! # Intrinsic Archimedean Centralizer -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicArchimedeanCentralizer.Intrinsic

noncomputable section

/-! Apply the full native archimedean lift-uniqueness conclusion to
actual local oscillator elements centralizing the geometric SU action. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.SiegelBranchData
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicUniqueLiftCentralizer.Intrinsic OAI.RepresentationTheory.Theta.Adelic.IntrinsicCoverTopology.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : Adelic.BallGeometryData.BallArithmeticData F d m H K)
variable {hd : d ≠ 0} {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K} {C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m}
variable (D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C P)

local instance (v : NumberField.InfinitePlace F) : MeasurableSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := borel _
local instance (v : NumberField.InfinitePlace F) : BorelSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := ⟨rfl⟩

theorem native_lift_centralizer (hu : Adelic.SiegelBranchData.ArchimedeanLiftUniqueness P hd C D) (v : Fin A.places)
    (b : Weil.AdelicSplitting.Vacuum.Construction.CoverAt F (3 * m) C.ψ (.inl (A.enumerate v)))
    (hb : ∀ g : Adelic.SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl (A.enumerate v))),
      Commute (Weil.AdelicSplitting.Vacuum.Construction.projectionAt F (3 * m) C.ψ (.inl (A.enumerate v)) b)
        (Weil.AdelicSplitting.Assembly.Construction.localDualAction F d 3 m H K P (.inl (A.enumerate v))
          (Adelic.FiniteSchwartz.localSUToPair F H K (.inl (A.enumerate v)) g)))
    (g : Adelic.SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl (A.enumerate v)))) :
    Commute b (Adelic.FiniteSchwartz.localSUSplitting F H K hd C P D (.inl (A.enumerate v)) g) := by
  let : SecondCountableTopology (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl (A.enumerate v))) :=
    (show Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl (A.enumerate v)) ≃ₜ ℝ from
      ⟨(A.real v).toEquiv,A.real_continuous v,A.real_inverse_continuous v⟩).secondCountableTopology
  let : IsTopologicalGroup (Weil.AdelicSplitting.Vacuum.Construction.CoverAt F (3 * m) C.ψ (.inl (A.enumerate v))) :=
    Adelic.IntrinsicCoverTopology.Intrinsic.localCover_isTopologicalGroup _ _ _
  apply IntrinsicUniqueLiftCentralizer.Intrinsic.unique_lift_commutes (Weil.AdelicSplitting.Vacuum.Construction.projectionAt F (3 * m) C.ψ (.inl (A.enumerate v)))
    (Adelic.FiniteSchwartz.localSUSplitting F H K hd C P D (.inl (A.enumerate v))) ?_ b ?_ g
  · intro t ht
    apply hu (A.enumerate v) t
    intro a
    exact (ht a).trans (D.covers (.inl (A.enumerate v)) (Adelic.FiniteSchwartz.localSUToPair F H K (.inl (A.enumerate v)) a))
  · intro a
    change Commute (Weil.AdelicSplitting.Vacuum.Construction.projectionAt F (3 * m) C.ψ (.inl (A.enumerate v)) b)
      (Weil.AdelicSplitting.Vacuum.Construction.projectionAt F (3 * m) C.ψ (.inl (A.enumerate v))
        (D.atPlace (.inl (A.enumerate v)) (Adelic.FiniteSchwartz.localSUToPair F H K (.inl (A.enumerate v)) a)))
    rw [D.covers]
    exact hb a

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicArchimedeanCentralizer.Intrinsic
