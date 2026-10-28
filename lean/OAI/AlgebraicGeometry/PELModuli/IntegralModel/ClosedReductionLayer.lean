import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CoherentClosedDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AnnihilatorSubobjects

/-! # Closed Reduction Layer -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ClosedReductionLayer

noncomputable section

/-! The canonical coherent layer obtained by restricting to a closed
subscheme. Its quotient descends to that actual closed subscheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

def closedModuleUnit {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    M ⟶ (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj M) :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M

def closedReductionKernel {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) : Y.Modules :=
  kernel (closedModuleUnit f M)

def closedReductionQuotient {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) : Y.Modules :=
  Abelian.coimage (closedModuleUnit f M)

def closedReductionSequence {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    ShortComplex Y.Modules :=
  ShortComplex.mk (kernel.ι (closedModuleUnit f M))
    (Abelian.coimage.π (closedModuleUnit f M)) (by simp)

theorem closedReductionSequence_shortExact {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    (closedReductionSequence f M).ShortExact := by
  change (ShortComplex.mk (kernel.ι (closedModuleUnit f M))
    (Abelian.coimage.π (closedModuleUnit f M)) _).ShortExact
  exact ⟨ShortComplex.cokernelSequence_exact (kernel.ι (closedModuleUnit f M))⟩

theorem closedReductionKernel_quasicoherent
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (M : Y.Modules) [M.IsQuasicoherent] : (closedReductionKernel f M).IsQuasicoherent := by
  have := SheafCohomology.Projective.QuasicoherentAffinePullback.quasicoherent_pullback_of_isAffineHom f M
  have := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom
    (M := (Scheme.Modules.pullback f).obj M) f
  exact SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_kernel (closedModuleUnit f M)

theorem closedReductionKernel_finiteType
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsClosedImmersion f]
    (M : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    (closedReductionKernel f M).IsFiniteType := by
  have := SheafCohomology.Projective.QuasicoherentAffinePullback.quasicoherent_pullback_of_isAffineHom f M
  have := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom
    (M := (Scheme.Modules.pullback f).obj M) f
  exact SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isFiniteType_kernel (closedModuleUnit f M)

theorem closedReductionQuotient_quasicoherent
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (M : Y.Modules) [M.IsQuasicoherent] : (closedReductionQuotient f M).IsQuasicoherent := by
  have : (kernel (closedModuleUnit f M)).IsQuasicoherent := closedReductionKernel_quasicoherent f M
  exact SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_cokernel (kernel.ι (closedModuleUnit f M))

theorem closedReductionQuotient_finiteType
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (M : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    (closedReductionQuotient f M).IsFiniteType := by
  have : (kernel (closedModuleUnit f M)).IsQuasicoherent := closedReductionKernel_quasicoherent f M
  exact SheafCohomology.Projective.CoherentQuotientFiniteType.Scheme.Modules.isFiniteType_cokernel (kernel.ι (closedModuleUnit f M))

theorem closedReductionQuotient_ideal_annihilates
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (M : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    letI := closedReductionQuotient_quasicoherent f M
    letI := closedReductionQuotient_finiteType f M
    f.ker ≤ CoherentAnnihilator.coherentAnnihilator (closedReductionQuotient f M) := by
  have := closedReductionQuotient_quasicoherent f M
  have := closedReductionQuotient_finiteType f M
  let P := (Scheme.Modules.pullback f).obj M
  have : P.IsQuasicoherent := SheafCohomology.Projective.QuasicoherentAffinePullback.quasicoherent_pullback_of_isAffineHom f M
  have : P.IsFiniteType := Finite.TypePullback.module_pullback_finiteType f M
  have := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom (M := P) f
  have := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isFiniteType_pushforward_of_isClosedImmersion (M := P) f
  exact (AnnihilatorSubobjects.closedIdeal_annihilates_pushforward f P).trans
    (AnnihilatorSubobjects.coherentAnnihilator_le_of_mono (Abelian.factorThruCoimage (closedModuleUnit f M)))

theorem closedReductionQuotient_exists_descent
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (M : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ N : X.Modules, N.IsQuasicoherent ∧ N.IsFiniteType ∧
      Nonempty ((Scheme.Modules.pushforward f).obj N ≅ closedReductionQuotient f M) := by
  have := closedReductionQuotient_quasicoherent f M
  have := closedReductionQuotient_finiteType f M
  exact CoherentClosedDescent.exists_coherent_closed_descent f (closedReductionQuotient f M)
    (closedReductionQuotient_ideal_annihilates f M)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ClosedReductionLayer
