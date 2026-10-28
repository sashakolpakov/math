import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsogenyComplement
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.EtaleDetection
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupLocus

/-! # Etale -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Etale.Construction

noncomputable section

/-!
A quotient with etale kernel is etale. The quotient diagonal is exhibited
as the equalizer of the difference map to the kernel and the identity-valued
map. This connects TorsionQuotient's torsion geometry to the actual FiniteDescent isogeny.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {A B H : Over S} [GrpObj A] [GrpObj B] [GrpObj H]

set_option backward.isDefEq.respectTransparency false in
/-- The relative quotient diagonal is open when its scheme kernel is etale. -/
theorem quotient_diagonal_open_of_etale_kernel
    (i : H ⟶ A) [IsMonHom i] [Mono i] [Etale H.hom]
    (f : A ⟶ B) [IsMonHom f]
    (hkernel : ∀ (T : Over S) (a : T ⟶ A),
      a ≫ f = 1 ↔ ∃! h : T ⟶ H, h ≫ i = a) :
    IsOpenImmersion (pullback.diagonal f).left := by
  let R := pullback f f
  let x : R ⟶ A := pullback.fst f f
  let y : R ⟶ A := pullback.snd f f
  have hdiff : (x / y) ≫ f = 1 := by
    rw [GrpObj.div_comp, show x ≫ f = y ≫ f from pullback.condition, div_self']
  obtain ⟨δ, hδ, _⟩ := (hkernel R (x / y)).mp hdiff
  have hdiag : pullback.diagonal f ≫ δ = 1 := by
    apply (cancel_mono i).mp
    rw [Category.assoc, hδ, GrpObj.comp_div, MonObj.one_comp]
    simp only [x, y, pullback.diagonal_fst, pullback.diagonal_snd, div_self']
  let E := equalizer δ (1 : R ⟶ H)
  let j : E ⟶ R := equalizer.ι δ (1 : R ⟶ H)
  let d : A ⟶ E := equalizer.lift (pullback.diagonal f)
    (hdiag.trans (MonObj.comp_one _).symm)
  let c : E ⟶ A := j ≫ x
  have hxy : j ≫ x = j ≫ y := by
    have he : j ≫ δ = 1 := (equalizer.condition δ (1 : R ⟶ H)).trans (MonObj.comp_one j)
    have he' := congrArg (fun z => z ≫ i) he
    rw [Category.assoc, hδ, GrpObj.comp_div, MonObj.one_comp, div_eq_one] at he'
    exact he'
  have hdc : d ≫ c = 𝟙 A := by
    change d ≫ (j ≫ pullback.fst f f) = 𝟙 A
    rw [← Category.assoc, equalizer.lift_ι, pullback.diagonal_fst]
  have hcd : c ≫ d = 𝟙 E := by
    apply equalizer.hom_ext
    change (c ≫ d) ≫ j = (𝟙 E) ≫ j
    rw [Category.assoc, equalizer.lift_ι, Category.id_comp]
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id]
      rfl
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id]
      exact hxy
  have : IsIso d := ⟨⟨c, hdc, hcd⟩⟩
  have : IsIso d.left := (Over.forget S).map_isIso d
  have : IsOpenImmersion j.left := EtaleDetection.Construction.equalizer_openImmersion δ 1
  have : IsOpenImmersion (d.left ≫ j.left) := inferInstance
  have hdj : d.left ≫ j.left = (pullback.diagonal f).left :=
    congrArg (fun z => z.left) (equalizer.lift_ι (pullback.diagonal f)
      (hdiag.trans (MonObj.comp_one _).symm))
  exact hdj ▸ this

set_option backward.isDefEq.respectTransparency false in
/-- The FiniteDescent quotient is etale once TorsionQuotient makes its kernel etale. -/
theorem quotient_etale_of_etale_kernel
    (i : H ⟶ A) [IsMonHom i] [Mono i] [Etale H.hom]
    (f : A ⟶ B) [IsMonHom f] [Flat f.left] [LocallyOfFinitePresentation f.left]
    (hkernel : ∀ (T : Over S) (a : T ⟶ A),
      a ≫ f = 1 ↔ ∃! h : T ⟶ H, h ≫ i = a) : Etale f.left := by
  have : IsOpenImmersion (pullback.diagonal f).left :=
    quotient_diagonal_open_of_etale_kernel i f hkernel
  let c := pullbackComparison (Over.forget S) f f
  have : IsIso c := inferInstance
  have hc : (pullback.diagonal f).left ≫ c = pullback.diagonal f.left := by
    apply pullback.hom_ext
    · simp only [c, Category.assoc, pullbackComparison_comp_fst]
      change ((pullback.diagonal f) ≫ pullback.fst f f).left = _
      rw [pullback.diagonal_fst]
      exact (pullback.diagonal_fst f.left).symm
    · simp only [c, Category.assoc, pullbackComparison_comp_snd]
      change ((pullback.diagonal f) ≫ pullback.snd f f).left = _
      rw [pullback.diagonal_snd]
      exact (pullback.diagonal_snd f.left).symm
  have hopen : IsOpenImmersion ((pullback.diagonal f).left ≫ c) := inferInstance
  have : IsOpenImmersion (pullback.diagonal f.left) := hc ▸ hopen
  exact Etale.of_formallyUnramified_of_flat f.left

/-- Apply the etaleness argument to the actual kernel and quotient
constructed earlier. Its geometric hypotheses are supplied by TorsionQuotient/FiniteDescent. -/
theorem constructed_quotient_etale
    (A : Picard.PoincareBundle.Epi.Construction.AbelianScheme S) (P : Over S)
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.toOver P) (R : F.Model)
    (n : ℕ) (hkilled : F.KilledBy n)
    (h_TorsionQuotient : Etale (TorsionQuotient.SubgroupFunctor.torsionScheme A.toOver n).hom)
    (B : Picard.PoincareBundle.Epi.Construction.AbelianScheme P.left)
    (f : Picard.PoincareBundle.Epi.Construction.AbelianScheme.Isogeny (IsogenyComplement.Construction.baseChangedAbelianScheme A P) B)
    (hkernel : ∀ (T : Over P.left) (a : T ⟶ (IsogenyComplement.Construction.baseChangedAbelianScheme A P).toOver),
      a ≫ f.hom = 1 ↔ ∃! h : T ⟶ (Subgroup.Construction.subgroupGroupScheme F R).X,
        h ≫ (Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom = a) : Etale f.hom.left := by
  let i := (Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom
  have hiMon : IsMonHom i := (Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.isMonHom_hom
  have : IsClosedImmersion i.left := Kernel.Inclusion.Construction.subgroupInclusion_closedImmersion F R
  have hiMono : Mono i := Over.mono_of_mono_left i
  have hHetale : Etale (Subgroup.Construction.subgroupGroupScheme F R).X.hom := by
    rw [Subgroup.Construction.subgroupGroupScheme_structureMap]
    exact SubgroupLocus.Construction.subgroup_model_etale F R n hkilled h_TorsionQuotient
  exact @quotient_etale_of_etale_kernel P.left
    (IsogenyComplement.Construction.baseChangedAbelianScheme A P).toOver B.toOver (Subgroup.Construction.subgroupGroupScheme F R).X
    (IsogenyComplement.Construction.baseChangedAbelianScheme A P).group B.group (Subgroup.Construction.subgroupGroupScheme F R).grp
    i hiMon hiMono hHetale f.hom inferInstance inferInstance
    inferInstance hkernel

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Etale.Construction
