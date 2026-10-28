import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Quotient

/-! # Prescribed -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescribed.Construction

noncomputable section

/-!
Identification of the quotient for an independently prescribed subgroup.
Homomorphisms is used through its two explicit clauses: the multiplicative subgroup
represents the kernel on every test scheme, and Frobenius is its fppf
quotient. The comparison and its projection equation are constructed here.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {A AF H K : Over S} [GrpObj A] [GrpObj AF]

abbrev subgroupQuotientProjection (i : H ⟶ A) :
    (BaseChange.Construction.fppfPoints S).obj A ⟶ BaseChange.Construction.subgroupQuotient i := coequalizer.π _ _

theorem subgroupTranslation_of_iso (i : H ⟶ A) (j : K ⟶ A)
    (e : H ≅ K) (he : e.hom ≫ j = i) :
    (e.hom ⊗ₘ 𝟙 A) ≫ ((fst K A ≫ j) * snd K A) =
      (fst H A ≫ i) * snd H A := by
  rw [MonObj.comp_mul]
  simp only [← Category.assoc, tensorHom_fst, tensorHom_snd, Category.comp_id]
  rw [Category.assoc, he]

def subgroupQuotientMapOfIso (i : H ⟶ A) (j : K ⟶ A)
    (e : H ≅ K) (he : e.hom ≫ j = i) : BaseChange.Construction.subgroupQuotient i ⟶ BaseChange.Construction.subgroupQuotient j :=
  coequalizer.desc (subgroupQuotientProjection j) (by
    have h := congrArg (fun f => (BaseChange.Construction.fppfPoints S).map (e.hom ⊗ₘ 𝟙 A) ≫ f)
      (coequalizer.condition ((BaseChange.Construction.fppfPoints S).map ((fst K A ≫ j) * snd K A))
        ((BaseChange.Construction.fppfPoints S).map (snd K A)))
    simpa only [← Category.assoc, ← Functor.map_comp,
      subgroupTranslation_of_iso i j e he, tensorHom_snd, Category.comp_id,
      BaseChange.Construction.subgroupQuotient, BaseChange.Construction.relationQuotient, subgroupQuotientProjection] using h)

theorem subgroupQuotientMapOfIso_projection (i : H ⟶ A) (j : K ⟶ A)
    (e : H ≅ K) (he : e.hom ≫ j = i) :
    subgroupQuotientProjection i ≫
      subgroupQuotientMapOfIso i j e he =
        subgroupQuotientProjection j :=
  coequalizer.π_desc _ _

/-- Equal embedded group schemes have canonically isomorphic constructed
quotients, with the same quotient projection. -/
def subgroupQuotientIsoOfIso (i : H ⟶ A) (j : K ⟶ A)
    (e : H ≅ K) (he : e.hom ≫ j = i) : BaseChange.Construction.subgroupQuotient i ≅ BaseChange.Construction.subgroupQuotient j := by
  have hrev : e.inv ≫ i = j := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  refine {
    hom := subgroupQuotientMapOfIso i j e he
    inv := subgroupQuotientMapOfIso j i e.symm hrev
    hom_inv_id := ?_
    inv_hom_id := ?_ }
  ·
    apply coequalizer.hom_ext
    change subgroupQuotientProjection i ≫
      subgroupQuotientMapOfIso i j e he ≫ _ = _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ subgroupQuotientMapOfIso j i e.symm hrev)
        (subgroupQuotientMapOfIso_projection i j e he)).trans
        ((subgroupQuotientMapOfIso_projection j i e.symm hrev).trans
          (Category.comp_id _).symm))
  ·
    apply coequalizer.hom_ext
    change subgroupQuotientProjection j ≫
      subgroupQuotientMapOfIso j i e.symm _ ≫ _ = _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ subgroupQuotientMapOfIso i j e he)
        (subgroupQuotientMapOfIso_projection j i e.symm hrev)).trans
        ((subgroupQuotientMapOfIso_projection i j e he).trans
          (Category.comp_id _).symm))

/-- Homomorphisms's kernel clause in universal-property form, so the prescribed
subgroup is an actual scheme and not just a collection of field points. -/
def PrescribedKernel (F : A ⟶ AF) (i : H ⟶ A) : Prop :=
  ∀ (T : Over S) (a : T ⟶ A), a ≫ F = 1 ↔
    ∃! h : T ⟶ H, h ≫ i = a

omit [GrpObj A] in
theorem prescribedKernel_kills (F : A ⟶ AF) (i : H ⟶ A)
    [Mono i] (h : PrescribedKernel F i) : i ≫ F = 1 := by
  apply (h H i).mpr
  refine ⟨𝟙 H, Category.id_comp i, ?_⟩
  intro a ha
  apply (cancel_mono i).mp
  exact ha.trans (Category.id_comp i).symm

def prescribedKernelForkIsLimit (F : A ⟶ AF) (i : H ⟶ A)
    [Mono i] (h : PrescribedKernel F i) :
    IsLimit (Fork.ofι i ((prescribedKernel_kills F i h).trans (MonObj.comp_one i).symm)) :=
  Fork.IsLimit.ofExistsUnique (fun t =>
    (h t.pt t.ι).mp (t.condition.trans (MonObj.comp_one t.ι)))

/-- Construct the comparison of the prescribed subgroup with the literal
scheme kernel. Homomorphisms supplies the universal property, not the comparison. -/
def prescribedKernelIso (F : A ⟶ AF) (i : H ⟶ A)
    [Mono i] (h : PrescribedKernel F i) : H ≅ Picard.Homomorphisms.Kernel.Construction.kernelScheme F := by
  let e := (prescribedKernelForkIsLimit F i h).conePointUniqueUpToIso (equalizerIsEqualizer F 1)
  exact e

omit [GrpObj A] in
theorem prescribedKernelIso_inclusion (F : A ⟶ AF) (i : H ⟶ A)
    [Mono i] (h : PrescribedKernel F i) :
    (prescribedKernelIso F i h).hom ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion F = i :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (prescribedKernelForkIsLimit F i h) (equalizerIsEqualizer F 1) WalkingParallelPair.zero

/-- The independently prescribed Frobenius-kernel quotient is represented
by the actual Frobenius target, conditional on the two explicit Homomorphisms clauses. -/
def prescribedFrobeniusQuotientIsoOfHomomorphisms (F : A ⟶ AF) [IsMonHom F]
    (i : H ⟶ A) [Mono i]
    (h_Homomorphisms_kernel : PrescribedKernel F i)
    (h_Homomorphisms_quotient : Picard.Homomorphisms.Quotient.Construction.IsFppfQuotientByKernel F) :
    BaseChange.Construction.subgroupQuotient i ≅ (BaseChange.Construction.fppfPoints S).obj AF :=
  subgroupQuotientIsoOfIso i (Picard.Homomorphisms.Kernel.Construction.kernelInclusion F)
    (prescribedKernelIso F i h_Homomorphisms_kernel)
    (prescribedKernelIso_inclusion F i h_Homomorphisms_kernel) ≪≫
      Quotient.Construction.kernelQuotientIsoOfHomomorphisms F h_Homomorphisms_quotient

theorem prescribedFrobeniusQuotientIsoOfHomomorphisms_projection
    (F : A ⟶ AF) [IsMonHom F] (i : H ⟶ A) [Mono i]
    (h_Homomorphisms_kernel : PrescribedKernel F i)
    (h_Homomorphisms_quotient : Picard.Homomorphisms.Quotient.Construction.IsFppfQuotientByKernel F) :
    subgroupQuotientProjection i ≫
        (prescribedFrobeniusQuotientIsoOfHomomorphisms F i h_Homomorphisms_kernel h_Homomorphisms_quotient).hom =
      (BaseChange.Construction.fppfPoints S).map F := by
  change subgroupQuotientProjection i ≫
    subgroupQuotientMapOfIso i (Picard.Homomorphisms.Kernel.Construction.kernelInclusion F)
      (prescribedKernelIso F i h_Homomorphisms_kernel)
      (prescribedKernelIso_inclusion F i h_Homomorphisms_kernel) ≫
      (Quotient.Construction.kernelQuotientIsoOfHomomorphisms F h_Homomorphisms_quotient).hom = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (Quotient.Construction.kernelQuotientIsoOfHomomorphisms F h_Homomorphisms_quotient).hom)
      (subgroupQuotientMapOfIso_projection i (Picard.Homomorphisms.Kernel.Construction.kernelInclusion F)
        (prescribedKernelIso F i h_Homomorphisms_kernel)
        (prescribedKernelIso_inclusion F i h_Homomorphisms_kernel))).trans
      (Quotient.Construction.kernelQuotientIsoOfHomomorphisms_projection F h_Homomorphisms_quotient))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescribed.Construction
