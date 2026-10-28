import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.FlasqueInjectives
import OAI.AlgebraicGeometry.CycleClass.Geometric.FlasqueLowDegree
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExtensionComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ConeQuasiIso
import Mathlib.Algebra.Homology.HomotopyCategory.Plus

/-! # Flasque Comparison -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.FlasqueComparison

noncomputable section

/-! Actual global sections preserve quasi-isomorphisms of nonnegative flasque abelian complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open OAI.AlgebraicGeometry.CycleClass.Geometric.FlasqueLowDegree.Cycles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}}

theorem abelianFlasqueGlobalSections_acyclic
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (he : K.Acyclic) :
    (CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex K).Acyclic :=
  fun n => CycleClass.Geometric.FlasqueLowDegree.Cycles.flasqueLowDegree_exactAt K hK (n + 1) (fun i _ => he i) n (Nat.lt_succ_self n)

theorem abelianBoundedFlasqueGlobalSections_acyclic
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℤ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (b : ℤ) [K.IsStrictlyGE b] (he : K.Acyclic) :
    (((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSections X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  let e := ComplexShape.embeddingUpIntGE b
  apply (HodgeConjecture.DegreeTwo.BoundedFlasqueSections.Constructions.strictSupportRestriction_acyclic_iff _ e).mpr
  exact abelianFlasqueGlobalSections_acyclic (K.restriction e) (fun n => hK (e.f n))
    ((HodgeConjecture.DegreeTwo.BoundedFlasqueSections.Constructions.strictSupportRestriction_acyclic_iff K e).mp he)

theorem abelianSheafBiprod_isFlasque (F G : TopCat.Sheaf AddCommGrpCat.{0} X)
    [TopCat.Sheaf.IsFlasque F] [TopCat.Sheaf.IsFlasque G] : TopCat.Sheaf.IsFlasque (F ⊞ G) where
  epi {U V} j := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro s
    let i₁ : F ⟶ F ⊞ G := biprod.inl
    let i₂ : G ⟶ F ⊞ G := biprod.inr
    let p₁ : F ⊞ G ⟶ F := biprod.fst
    let p₂ : F ⊞ G ⟶ G := biprod.snd
    obtain ⟨u, hu⟩ := (AddCommGrpCat.epi_iff_surjective (F.obj.map j)).mp inferInstance (p₁.hom.app V s)
    obtain ⟨v, hv⟩ := (AddCommGrpCat.epi_iff_surjective (G.obj.map j)).mp inferInstance (p₂.hom.app V s)
    refine ⟨i₁.hom.app U u + i₂.hom.app U v, ?_⟩
    have h₁ := ConcreteCategory.congr_hom (i₁.hom.naturality j) u
    have h₂ := ConcreteCategory.congr_hom (i₂.hom.naturality j) v
    change i₁.hom.app V (F.obj.map j u) = (F ⊞ G).obj.map j (i₁.hom.app U u) at h₁
    change i₂.hom.app V (G.obj.map j v) = (F ⊞ G).obj.map j (i₂.hom.app U v) at h₂
    rw [map_add, ← h₁, ← h₂, hu, hv]
    have hid : p₁.hom.app V ≫ i₁.hom.app V + p₂.hom.app V ≫ i₂.hom.app V = 𝟙 _ :=
      congrArg (fun f => f.hom.app V) (biprod.total (X := F) (Y := G))
    exact ConcreteCategory.congr_hom hid s

theorem abelianFlasque_mappingCone
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℤ} (f : K ⟶ L)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (hL : ∀ n, TopCat.Sheaf.IsFlasque (L.X n)) (n : ℤ) :
    TopCat.Sheaf.IsFlasque ((CochainComplex.mappingCone f).X n) := by
  have := hK (n + 1)
  have := hL n
  have := abelianSheafBiprod_isFlasque (K.X (n + 1)) (L.X n)
  exact CycleClass.Geometric.FlasqueLowDegree.Cycles.flasqueSheaf_of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod f n (n + 1) rfl).symm

theorem abelianBoundedFlasqueGlobalSections_quasiIso
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℤ} (f : K ⟶ L)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (hL : ∀ n, TopCat.Sheaf.IsFlasque (L.X n))
    (b : ℤ) [K.IsStrictlyGE b] [L.IsStrictlyGE b] [QuasiIso f] :
    QuasiIso (((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSections X).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have := CochainComplex.isStrictlyGE_mappingCone f b b (b - 1) (by omega) (by omega)
  apply HodgeConjecture.DegreeTwo.ConeQuasiIso.Constructions.functorQuasiIso_of_mappingCone_acyclic
  exact abelianBoundedFlasqueGlobalSections_acyclic (CochainComplex.mappingCone f)
    (abelianFlasque_mappingCone f hK hL) (b - 1) ((HodgeConjecture.DegreeTwo.ConeQuasiIso.Constructions.cochainQuasiIso_iff_mappingCone_acyclic f).mp inferInstance)

theorem abelianFlasqueComplex_extend
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (i : ℤ) :
    TopCat.Sheaf.IsFlasque ((K.extend ComplexShape.embeddingUpNat).X i) := by
  by_cases hi : ∃ n, ComplexShape.embeddingUpNat.f n = i
  · obtain ⟨n, hn⟩ := hi
    have := hK n
    exact CycleClass.Geometric.FlasqueLowDegree.Cycles.flasqueSheaf_of_iso (K.extendXIso ComplexShape.embeddingUpNat hn).symm
  · exact CycleClass.Geometric.FlasqueLowDegree.Cycles.flasqueSheaf_of_isZero _ (K.isZero_extend_X ComplexShape.embeddingUpNat i (by simpa using hi))

theorem abelianFlasqueGlobalSections_quasiIso
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ} (f : K ⟶ L)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (hL : ∀ n, TopCat.Sheaf.IsFlasque (L.X n))
    [QuasiIso f] :
    QuasiIso (((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSections X).mapHomologicalComplex (ComplexShape.up ℕ)).map f) := by
  have := abelianBoundedFlasqueGlobalSections_quasiIso
    (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat)
    (abelianFlasqueComplex_extend K hK) (abelianFlasqueComplex_extend L hL) 0
  exact HodgeConjecture.DegreeTwo.ExtensionComparison.Constructions.functorQuasiIso_of_extended ComplexShape.embeddingUpNat (CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSections X) f

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.FlasqueComparison
