import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BaseChangeGroup
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Assembly

/-! # Torsion Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.TorsionBaseChange.Construction

noncomputable section

/-! Actual torsion group schemes commute with arbitrary base change.
The comparison is constructed from the all-test kernel property and
retains the original inclusion into the pulled-back abelian scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

attribute [local instance] BaseChange.Construction.pulledBackGroup

section KernelComparison

variable {S : Scheme.{u}} {A B H K : Over S} [GrpObj A] [GrpObj B]
variable (p : A ⟶ B) (i : H ⟶ A) (j : K ⟶ A) [Mono i] [Mono j]
variable (hi : Prescribed.Construction.PrescribedKernel p i) (hj : Prescribed.Construction.PrescribedKernel p j)

def prescribedKernelComparisonIso : H ≅ K :=
  Prescribed.Construction.prescribedKernelIso p i hi ≪≫ (Prescribed.Construction.prescribedKernelIso p j hj).symm

omit [GrpObj A] in
theorem prescribedKernelComparisonIso_inclusion :
    (prescribedKernelComparisonIso p i j hi hj).hom ≫ j = i := by
  have h : (Prescribed.Construction.prescribedKernelIso p j hj).inv ≫ j = Picard.Homomorphisms.Kernel.Construction.kernelInclusion p := by
    apply (Iso.inv_comp_eq _).mpr
    exact (Prescribed.Construction.prescribedKernelIso_inclusion p j hj).symm
  change ((Prescribed.Construction.prescribedKernelIso p i hi).hom ≫ (Prescribed.Construction.prescribedKernelIso p j hj).inv) ≫ j = i
  rw [Category.assoc, h]
  exact Prescribed.Construction.prescribedKernelIso_inclusion p i hi

end KernelComparison

variable {S T : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (f : T ⟶ S) (m : ℕ)

omit f in
theorem torsion_prescribedKernel : Prescribed.Construction.PrescribedKernel (A.multiplication m) (A.torsionInclusion m) := by
  intro U a
  rw [A.comp_multiplication]
  constructor
  · intro ha
    let z := (A.torsionSchemePointsEquiv m U).symm ⟨a, ha⟩
    have hz : z ≫ A.torsionInclusion m = a :=
      congrArg Subtype.val ((A.torsionSchemePointsEquiv m U).apply_symm_apply ⟨a, ha⟩)
    refine ⟨z, hz, ?_⟩
    intro w hw
    exact (cancel_mono (A.torsionInclusion m)).mp (hw.trans hz.symm)
  · rintro ⟨z, hz, _⟩
    rw [← hz, ← MonObj.comp_pow, A.torsionInclusion_pow, MonObj.comp_one]

theorem multiplication_baseChange :
    (Over.pullback f).map (A.multiplication m) = (A.pullback f).multiplication m := by
  change (Over.pullback f).map ((𝟙 A.scheme) ^ m) = (𝟙 ((Over.pullback f).obj A.scheme)) ^ m
  exact (map_pow (Over.pullback f).homMonoidHom _ m).trans
    (congrArg (fun a => a ^ m) ((Over.pullback f).map_id A.scheme))

def torsionInclusionBaseChange :
    (Over.pullback f).obj (A.torsionScheme m) ⟶ (A.pullback f).scheme :=
  (Over.pullback f).map (A.torsionInclusion m)

instance torsionInclusionBaseChange_mono : Mono (torsionInclusionBaseChange A f m) :=
  (Over.pullback f).map_mono (A.torsionInclusion m)

instance torsionInclusionBaseChange_isMonHom : IsMonHom (torsionInclusionBaseChange A f m) := by
  change IsMonHom ((Over.pullback f).map (A.torsionInclusion m))
  exact Functor.map.instIsMonHom (F := Over.pullback f) (f := A.torsionInclusion m)

theorem torsion_prescribedKernel_baseChange :
    Prescribed.Construction.PrescribedKernel ((A.pullback f).multiplication m) (torsionInclusionBaseChange A f m) := by
  change Prescribed.Construction.PrescribedKernel ((A.pullback f).multiplication m) ((Over.pullback f).map (A.torsionInclusion m))
  rw [← multiplication_baseChange A f m]
  exact KernelBaseChange.Construction.prescribedKernel_pullback f (A.multiplication m) (A.torsionInclusion m) (torsion_prescribedKernel A m)

def torsionSchemeBaseChangeIso :
    (Over.pullback f).obj (A.torsionScheme m) ≅ (A.pullback f).torsionScheme m :=
  prescribedKernelComparisonIso ((A.pullback f).multiplication m)
    (torsionInclusionBaseChange A f m) ((A.pullback f).torsionInclusion m)
    (torsion_prescribedKernel_baseChange A f m) (torsion_prescribedKernel (A.pullback f) m)

theorem torsionSchemeBaseChangeIso_inclusion :
    (torsionSchemeBaseChangeIso A f m).hom ≫ (A.pullback f).torsionInclusion m =
      torsionInclusionBaseChange A f m :=
  prescribedKernelComparisonIso_inclusion _ _ _ _ _

instance torsionSchemeBaseChangeIso_isMonHom : IsMonHom (torsionSchemeBaseChangeIso A f m).hom := by
  have : IsMonHom ((torsionSchemeBaseChangeIso A f m).hom ≫ (A.pullback f).torsionInclusion m) := by
    rw [torsionSchemeBaseChangeIso_inclusion]
    infer_instance
  exact BaseChangeGroup.Construction.isMonHom_of_mono_postcomp (torsionSchemeBaseChangeIso A f m).hom
    ((A.pullback f).torsionInclusion m)

def torsionGroupBaseChangeIso :
    (Over.pullback f).mapGrp.obj (Assembly.Construction.torsionGroup A m) ≅ Assembly.Construction.torsionGroup (A.pullback f) m :=
  Grp.mkIso' (torsionSchemeBaseChangeIso A f m)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.TorsionBaseChange.Construction
