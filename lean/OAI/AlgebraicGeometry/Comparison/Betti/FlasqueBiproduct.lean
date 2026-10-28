import OAI.AlgebraicGeometry.CycleClass.Geometric.FlasqueLowDegree
import OAI.AlgebraicTopology.Cohomology.Singular.OpenSheafComparison
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.SheafForget

/-! # Flasque Biproduct -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.FlasqueBiproduct

noncomputable section

section

/-!
# Sections of acyclic complexes of flasque complex sheaves

The proof uses actual surjectivity of restrictions and sheaf gluing.
Successive cokernels remain flasque, so taking sections preserves the
incoming cokernels and hence exactness. This adapts the abelian-group
argument in `Cycles.FlasqueLowDegree` to the complex coefficient category.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

abbrev ComplexSheaves (X : TopCat.{0}) := TopCat.Sheaf (ModuleCat.{0} ℂ) X

variable {X : TopCat.{0}}

def sections (U : Opens X) : ComplexSheaves X ⥤ ModuleCat.{0} ℂ :=
  AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.sheafSectionsFunctor X U

instance sectionsAdditive (U : Opens X) : (sections U).Additive :=
  inferInstanceAs ((AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.sheafSectionsFunctor (R := ℂ) X U).Additive)

instance sectionsPreservesFiniteLimits (U : Opens X) : PreservesFiniteLimits (sections U) := by
  exact comp_preservesFiniteLimits
    (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ))
    ((evaluation (Opens X)ᵒᵖ (ModuleCat.{0} ℂ)).obj (op U))

theorem flasque_of_iso {F G : ComplexSheaves X} (e : F ≅ G)
    [TopCat.Sheaf.IsFlasque F] : TopCat.Sheaf.IsFlasque G := by
  let e' := (TopCat.Sheaf.forget (ModuleCat.{0} ℂ) X).mapIso e
  constructor
  intro U V i
  have he : Epi (e'.hom.app U ≫ G.obj.map i) := by
    change Epi (e'.hom.app U ≫ ((TopCat.Sheaf.forget (ModuleCat.{0} ℂ) X).obj G).map i)
    rw [← e'.hom.naturality]
    have : Epi (((TopCat.Sheaf.forget (ModuleCat.{0} ℂ) X).obj F).map i) :=
      inferInstanceAs (Epi (F.obj.map i))
    infer_instance
  exact epi_of_epi (e'.hom.app U) (G.obj.map i)

theorem sections_shortExact (U : Opens X) (S : ShortComplex (ComplexSheaves X))
    (hS : S.ShortExact) [TopCat.Sheaf.IsFlasque S.X₁] :
    (S.map (sections U)).ShortExact := by
  have hleft := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (sections U)).1 inferInstance S hS
  have hep : Epi ((sections U).map S.g) := by
    change Epi (S.g.hom.app (op U))
    exact Complex.SheafForget.Flasque.flasque_section_epi U S hS
  exact ShortComplex.ShortExact.mk' hleft.1 hleft.2 hep

variable (K : CochainComplex (ComplexSheaves X) ℕ)
  (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (hacyclic : K.Acyclic)

include hK hacyclic

theorem opcycles_flasque (n : ℕ) : TopCat.Sheaf.IsFlasque (K.opcycles n) := by
  induction n with
  | zero =>
    have := hK 0
    exact flasque_of_iso K.opcycles₀Iso
  | succ n ih =>
    have := ih
    have := hK (n + 1)
    exact Complex.SheafForget.Flasque.flasque_of_shortExact₁₂ (CycleClass.Geometric.FlasqueLowDegree.Cycles.opcyclesSuccessorSequence K n)
      (CycleClass.Geometric.FlasqueLowDegree.Cycles.opcyclesSuccessorSequence_shortExact K n (hacyclic n))

theorem sections_pOpcycles_epi (U : Opens X) (n : ℕ) :
    Epi ((sections U).map (K.pOpcycles n)) := by
  cases n with
  | zero => infer_instance
  | succ n =>
    have := opcycles_flasque K hK hacyclic n
    exact (sections_shortExact U (CycleClass.Geometric.FlasqueLowDegree.Cycles.opcyclesSuccessorSequence K n)
      (CycleClass.Geometric.FlasqueLowDegree.Cycles.opcyclesSuccessorSequence_shortExact K n (hacyclic n))).epi_g

theorem sections_preserves_incoming_cokernel (U : Opens X) (n : ℕ) :
    PreservesColimit (parallelPair (K.sc n).f 0) (sections U) := by
  cases n with
  | zero =>
    apply preservesCokernel_zero'
    change K.d ((ComplexShape.up ℕ).prev 0) 0 = 0
    simp
  | succ n =>
    change PreservesColimit
      (parallelPair (K.d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1)) 0) (sections U)
    rw [CochainComplex.prev_nat_succ]
    have := opcycles_flasque K hK hacyclic n
    have := sections_pOpcycles_epi K hK hacyclic U n
    let S := CycleClass.Geometric.FlasqueLowDegree.Cycles.opcyclesSuccessorSequence K n
    have hS := sections_shortExact U S
      (CycleClass.Geometric.FlasqueLowDegree.Cycles.opcyclesSuccessorSequence_shortExact K n (hacyclic n))
    have := hS.epi_g
    refine preservesColimit_of_preserves_colimit_cocone
      (K.opcyclesIsCokernel n (n + 1) (by simp)) ?_
    apply (CokernelCofork.isColimitMapCoconeEquiv _ (sections U)).2
    exact isCokernelEpiComp hS.exact.gIsCokernel ((sections U).map (K.pOpcycles n))
      (hg := sections_pOpcycles_epi K hK hacyclic U n) (by
      change (sections U).map (K.d n (n + 1)) =
        (sections U).map (K.pOpcycles n) ≫ (sections U).map (K.fromOpcycles n (n + 1))
      rw [← Functor.map_comp, HomologicalComplex.p_fromOpcycles])

/-- Every actual open-section complex of an acyclic flasque complex is acyclic. -/
theorem sections_acyclic (U : Opens X) :
    (((sections U).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).Acyclic := by
  intro n
  have := sections_preserves_incoming_cokernel K hK hacyclic U n
  have : (sections U).PreservesRightHomologyOf (K.sc n) := by
    constructor
    intro h
    exact { f := inferInstance, g' := inferInstance }
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((sections U).map_isZero (hacyclic n).isZero_homology).of_iso
    ((K.sc n).mapHomologyIso' (sections U))

end

/-! Flasqueness of an actual biproduct, by lifting its two section components. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

variable {X : TopCat.{0}} (F G : ComplexSheaves X)
  [TopCat.Sheaf.IsFlasque F] [TopCat.Sheaf.IsFlasque G]

theorem biprod_flasque : TopCat.Sheaf.IsFlasque (F ⊞ G) := by
  constructor
  intro U V i
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro s
  obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective (F.obj.map i)).mp inferInstance
    ((biprod.fst : F ⊞ G ⟶ F).hom.app V s)
  obtain ⟨b, hb⟩ := (ModuleCat.epi_iff_surjective (G.obj.map i)).mp inferInstance
    ((biprod.snd : F ⊞ G ⟶ G).hom.app V s)
  refine ⟨(biprod.inl : F ⟶ F ⊞ G).hom.app U a +
    (biprod.inr : G ⟶ F ⊞ G).hom.app U b, ?_⟩
  have hla := ConcreteCategory.congr_hom ((biprod.inl : F ⟶ F ⊞ G).hom.naturality i) a
  have hlb := ConcreteCategory.congr_hom ((biprod.inr : G ⟶ F ⊞ G).hom.naturality i) b
  change (biprod.inl : F ⟶ F ⊞ G).hom.app V (F.obj.map i a) =
    (F ⊞ G).obj.map i ((biprod.inl : F ⟶ F ⊞ G).hom.app U a) at hla
  change (biprod.inr : G ⟶ F ⊞ G).hom.app V (G.obj.map i b) =
    (F ⊞ G).obj.map i ((biprod.inr : G ⟶ F ⊞ G).hom.app U b) at hlb
  rw [map_add, ← hla, ← hlb, ha, hb]
  have htotal := congrArg (fun k : F ⊞ G ⟶ F ⊞ G => k.hom.app V)
    (show (biprod.fst : F ⊞ G ⟶ F) ≫ biprod.inl +
      (biprod.snd : F ⊞ G ⟶ G) ≫ biprod.inr = 𝟙 (F ⊞ G) from biprod.total)
  exact ConcreteCategory.congr_hom htotal s

end

end OAI.AlgebraicGeometry.Comparison.Betti.FlasqueBiproduct
