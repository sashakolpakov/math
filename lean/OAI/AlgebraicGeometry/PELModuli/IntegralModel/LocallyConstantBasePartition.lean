import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ParameterSum
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.ParameterPoints

/-! # Locally Constant Base Partition -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LocallyConstantBasePartition

noncomputable section

/-! A locally constant base index induces an actual disjoint partition
of every test scheme. Maps to a sum whose components have the prescribed
indices factor uniquely on each test stratum. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace FiniteBasePartition
variable {S : Scheme.{0}} {I : Type} (c : LocallyConstant S I) (T : Over S)

def testIndex : LocallyConstant T.left I := c.comap ⟨T.hom, T.hom.continuous⟩

def testPart (i : I) : Over S := AbelianModuli.HilbertConstruction.Open.ParameterPoints.openParameterScheme T (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (testIndex c T) i)

def testPartInclusion (i : I) : testPart c T i ⟶ T :=
  AbelianModuli.HilbertConstruction.Open.ParameterPoints.openParameterInclusion T (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (testIndex c T) i)

def testPartitionIsColimit :
    IsColimit (Cofan.mk T.left (fun i => (testPartInclusion c T i).left)) :=
  Classical.choice ((Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
    (Cofan.mk T.left (fun i => (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (testIndex c T) i).ι))).mpr
      (inferInstanceAs (IsIso (Sigma.desc (fun i => (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (testIndex c T) i).ι)))))

theorem testPart_index (i : I) (t : (testPart c T i).left) : c ((testPart c T i).hom t) = i := t.property

variable {T}

theorem sumParameter_factor_at_index (Z : I → Over S)
    (hZ : ∀ i, ∀ z : (Z i).left, c ((Z i).hom z) = i)
    (f : T ⟶ Finite.ParameterSum.FiniteBasePartition.sumParameter Z) (i : I) (hT : ∀ t : T.left, c (T.hom t) = i) :
    ∃! q : T ⟶ Z i, q ≫ Finite.ParameterSum.FiniteBasePartition.sumParameterInclusion Z i = f := by
  have hrange : Set.range f.left ⊆ Set.range (Finite.ParameterSum.FiniteBasePartition.sumParameterInclusion Z i).left := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨k, z, hz⟩ := Finite.ParameterSum.FiniteBasePartition.sumParameter_component Z (f.left t)
    have hp : (Z k).hom z = T.hom t := by
      have h₁ := congrArg (fun g : (Z k).left ⟶ S => g z) (Finite.ParameterSum.FiniteBasePartition.sumParameterInclusion Z k).w
      have h₂ := congrArg (fun g : T.left ⟶ S => g t) f.w
      exact h₁.symm.trans ((congrArg (fun x => (Finite.ParameterSum.FiniteBasePartition.sumParameter Z).hom x) hz).trans h₂)
    have hki : k = i := (hZ k z).symm.trans ((congrArg c hp).trans (hT t))
    subst k
    exact ⟨z, hz⟩
  have : IsOpenImmersion (Finite.ParameterSum.FiniteBasePartition.sumParameterInclusion Z i).left :=
    inferInstanceAs (IsOpenImmersion (Sigma.ι (fun i => (Z i).left) i))
  let q := IsOpenImmersion.lift (Finite.ParameterSum.FiniteBasePartition.sumParameterInclusion Z i).left f.left hrange
  have hq : q ≫ (Finite.ParameterSum.FiniteBasePartition.sumParameterInclusion Z i).left = f.left := IsOpenImmersion.lift_fac _ _ _
  let q' : T ⟶ Z i := Over.homMk q (by
    rw [← (Finite.ParameterSum.FiniteBasePartition.sumParameterInclusion Z i).w, ← Category.assoc, hq]
    exact f.w)
  have : Mono (Finite.ParameterSum.FiniteBasePartition.sumParameterInclusion Z i) := Over.mono_of_mono_left _
  refine ⟨q', Over.OverMorphism.ext hq, ?_⟩
  intro p hp
  apply (cancel_mono (Finite.ParameterSum.FiniteBasePartition.sumParameterInclusion Z i)).mp
  exact hp.trans (Over.OverMorphism.ext hq).symm

end FiniteBasePartition

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LocallyConstantBasePartition
