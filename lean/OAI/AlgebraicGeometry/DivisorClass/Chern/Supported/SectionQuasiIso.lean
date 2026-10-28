import OAI.AlgebraicGeometry.CycleClass.Geometric.SupportStalkVanishes
import OAI.AlgebraicTopology.Cohomology.Singular.ShortExactQuasiIso

/-! # Section Quasi Iso -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.SectionQuasiIso

noncomputable section

section

/-! Actual maps of sheaf complexes induce maps of their closed-support kernels. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [Ring R] {X : TopCat.{0}} (O : Opens X)
variable {K L N : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ}

theorem sheafRestrictionComplex_naturality (f : K ⟶ L) :
    CycleClass.Geometric.SupportStalkVanishes.Cohomology.sheafRestrictionComplex O K ≫
      ((CycleClass.Geometric.SheafClosedSupport.Cohomology.openRestrictionPushforwardFunctor O).mapHomologicalComplex (ComplexShape.up ℕ)).map f =
    f ≫ CycleClass.Geometric.SupportStalkVanishes.Cohomology.sheafRestrictionComplex O L := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact ((CycleClass.Geometric.SheafClosedSupport.Cohomology.sheafRestrictionToOpenNatTrans O).naturality (f.f n)).symm

instance supportedSheafComplexInclusion_mono : Mono (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O K) :=
  inferInstanceAs (Mono (kernel.ι (CycleClass.Geometric.SupportStalkVanishes.Cohomology.sheafRestrictionComplex O K)))

def supportedSheafComplexMap (f : K ⟶ L) :
    CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O K ⟶ CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O L :=
  kernel.map (CycleClass.Geometric.SupportStalkVanishes.Cohomology.sheafRestrictionComplex O K) (CycleClass.Geometric.SupportStalkVanishes.Cohomology.sheafRestrictionComplex O L) f
    (((CycleClass.Geometric.SheafClosedSupport.Cohomology.openRestrictionPushforwardFunctor O).mapHomologicalComplex (ComplexShape.up ℕ)).map f)
    (sheafRestrictionComplex_naturality O f)

theorem supportedSheafComplexMap_inclusion (f : K ⟶ L) :
    supportedSheafComplexMap O f ≫ CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O L =
      CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O K ≫ f :=
  kernel.lift_ι _ _ _

theorem supportedSheafComplexMap_id :
    supportedSheafComplexMap O (𝟙 K) = 𝟙 (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O K) := by
  apply (cancel_mono (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O K)).mp
  rw [supportedSheafComplexMap_inclusion, Category.id_comp, Category.comp_id]

theorem supportedSheafComplexMap_comp (f : K ⟶ L) (g : L ⟶ N) :
    supportedSheafComplexMap O (f ≫ g) =
      supportedSheafComplexMap O f ≫ supportedSheafComplexMap O g := by
  apply (cancel_mono (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O N)).mp
  calc
    _ = CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O K ≫ (f ≫ g) :=
      supportedSheafComplexMap_inclusion O (f ≫ g)
    _ = (supportedSheafComplexMap O f ≫ CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O L) ≫ g := by
      rw [supportedSheafComplexMap_inclusion, Category.assoc]
    _ = _ := by
      rw [Category.assoc (supportedSheafComplexMap O f) (supportedSheafComplexMap O g),
        supportedSheafComplexMap_inclusion O g]
      exact Category.assoc _ _ _

end

/-!
Comparisons of flasque complexes that are quasi-isomorphisms on the two
actual open-section complexes remain quasi-isomorphisms with the prescribed
closed support. This is the first-term five lemma for the restriction kernels.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [Ring R] {X : TopCat.{0}} (O : Opens X)
variable (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ)

def supportedSheafKernelSequence :
    ShortComplex (CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ) :=
  ShortComplex.mk (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O K) (CycleClass.Geometric.SupportStalkVanishes.Cohomology.sheafRestrictionComplex O K)
    (kernel.condition (CycleClass.Geometric.SupportStalkVanishes.Cohomology.sheafRestrictionComplex O K))

theorem supportedSheafKernelSequence_sections_shortExact
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (U : Opens X) :
    ((supportedSheafKernelSequence O K).map
      ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := R) U).mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact := by
  let F := (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := R) U).mapHomologicalComplex (ComplexShape.up ℕ)
  have hg : Epi (F.map (CycleClass.Geometric.SupportStalkVanishes.Cohomology.sheafRestrictionComplex O K)) := by
    apply HomologicalComplex.epi_of_epi_f
    intro n
    have := hK n
    change Epi ((K.X n).obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op)
    infer_instance
  have hm : Mono (F.map (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O K)) := inferInstance
  exact ShortComplex.ShortExact.mk'
    ((ShortComplex.kernelSequence_exact (CycleClass.Geometric.SupportStalkVanishes.Cohomology.sheafRestrictionComplex O K)).map_of_mono_of_preservesKernel
      F inferInstance inferInstance) hm hg

variable {K} {L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ} (f : K ⟶ L)

def supportedSheafKernelSequenceMap :
    supportedSheafKernelSequence O K ⟶ supportedSheafKernelSequence O L where
  τ₁ := supportedSheafComplexMap O f
  τ₂ := f
  τ₃ := ((CycleClass.Geometric.SheafClosedSupport.Cohomology.openRestrictionPushforwardFunctor O).mapHomologicalComplex (ComplexShape.up ℕ)).map f
  comm₁₂ := supportedSheafComplexMap_inclusion O f
  comm₂₃ := (sheafRestrictionComplex_naturality O f).symm

theorem supportedSheafSectionsMap_quasiIso
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
    (hL : ∀ n, TopCat.Sheaf.IsFlasque (L.X n)) (U : Opens X)
    (hU : QuasiIso (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := R) U).mapHomologicalComplex
      (ComplexShape.up ℕ)).map f))
    (hO : QuasiIso (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := R) (U ⊓ O)).mapHomologicalComplex
      (ComplexShape.up ℕ)).map f)) :
    QuasiIso (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := R) U).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (supportedSheafComplexMap O f)) :=
  AlgebraicTopology.Cohomology.Singular.ShortExactQuasiIso.quasiIso_first_of_shortExact
    ((((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := R) U).mapHomologicalComplex (ComplexShape.up ℕ)).mapShortComplex).map
      (supportedSheafKernelSequenceMap O f))
    (supportedSheafKernelSequence_sections_shortExact O K hK U)
    (supportedSheafKernelSequence_sections_shortExact O L hL U) hU hO

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.SectionQuasiIso
