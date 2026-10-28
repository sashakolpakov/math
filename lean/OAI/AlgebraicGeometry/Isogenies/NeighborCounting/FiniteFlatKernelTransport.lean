import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Base
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Properties

/-! # Finite Flat Kernel Transport -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! Transport the actual finite flat kernel under base change and a
group isomorphism, retaining its inclusion and all-test relative model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Base
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

universe u

def Kernel.Properties.FiniteFlatKernel.pullback {S T : Scheme.{u}} {A : Over S} [GrpObj A]
    (K : Kernel.Properties.FiniteFlatKernel A) (f : T ⟶ S) : Kernel.Properties.FiniteFlatKernel ((Over.pullback f).obj A) := by
  let : IsFinite K.carrier.hom := K.finite
  let : Flat K.carrier.hom := K.flat
  let : LocallyOfFinitePresentation K.carrier.hom := K.finitePresentation
  exact {
    carrier := (Over.pullback f).obj K.carrier
    inclusion := (Over.pullback f).map K.inclusion
    group := inferInstance
    isHom := Functor.map.instIsMonHom (F := Over.pullback f) (f := K.inclusion) K.carrier A
    finite := by change IsFinite (Limits.pullback.snd K.carrier.hom f); infer_instance
    flat := by change Flat (Limits.pullback.snd K.carrier.hom f); infer_instance
    finitePresentation := by
      change LocallyOfFinitePresentation (Limits.pullback.snd K.carrier.hom f)
      infer_instance
    closed := MorphismProperty.overPullbackMap (P := @IsClosedImmersion.{u}) f K.inclusion K.closed }

def Kernel.Properties.FiniteFlatKernel.mapIso {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
    (K : Kernel.Properties.FiniteFlatKernel A) (e : A ≅ B) [IsMonHom e.hom] : Kernel.Properties.FiniteFlatKernel B := by
  let : IsClosedImmersion K.inclusion.left := K.closed
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  exact {
    carrier := K.carrier
    inclusion := K.inclusion ≫ e.hom
    group := K.group
    isHom := inferInstanceAs (IsMonHom (K.inclusion ≫ e.hom))
    finite := K.finite
    flat := K.flat
    finitePresentation := K.finitePresentation
    closed := inferInstanceAs (IsClosedImmersion (K.inclusion.left ≫ e.hom.left)) }

theorem Kernel.Properties.FiniteFlatKernel.pullback_inclusion {S T : Scheme.{u}} {A : Over S} [GrpObj A]
    (K : Kernel.Properties.FiniteFlatKernel A) (f : T ⟶ S) :
    (K.pullback f).inclusion = (Over.pullback f).map K.inclusion := rfl

theorem Kernel.Properties.FiniteFlatKernel.mapIso_inclusion {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
    (K : Kernel.Properties.FiniteFlatKernel A) (e : A ≅ B) [IsMonHom e.hom] :
    (K.mapIso e).inclusion = K.inclusion ≫ e.hom := rfl

def Kernel.Properties.FiniteFlatKernel.relativeModel {S : Scheme.{u}} {A : Over S} [GrpObj A] [IsCommMonObj A]
    (K : Kernel.Properties.FiniteFlatKernel A) (P : Over S) : (Kernel.Base.fixedKernelFamily (P := P) K.inclusion).Model := by
  let : IsFinite K.carrier.hom := K.finite
  let : Flat K.carrier.hom := K.flat
  let : LocallyOfFinitePresentation K.carrier.hom := K.finitePresentation
  let : IsClosedImmersion K.inclusion.left := K.closed
  have : Mono K.inclusion := Over.mono_of_mono_left K.inclusion
  exact Kernel.Base.fixedKernelFamily_model K.inclusion

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
