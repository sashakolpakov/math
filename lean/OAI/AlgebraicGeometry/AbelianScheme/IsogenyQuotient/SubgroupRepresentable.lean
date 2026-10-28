import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupLocus
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Unit

/-! # Subgroup Representable -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupRepresentable.Construction

/-!
The chosen-block subgroup functor is finite etale representable, conditional
on TorsionQuotient for the actual ambient subgroup functor. The projector condition is
constructed as a clopen locus and its Yoneda representation is proved.
`RepresentableBy` avoids an artificial universe restriction on the functor
of subgroups over all test schemes; it is the usual natural representation.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {A : Over S} [GrpObj A] [IsCommMonObj A]

/-- The parameter open, regarded as a scheme over the original base. -/
def openParameter (P : Over S) (U : P.left.Opens) : Over S :=
  Over.mk (U.ι ≫ P.hom)

def openParameterι (P : Over S) (U : P.left.Opens) : openParameter P U ⟶ P :=
  Over.homMk U.ι rfl

/-- Yoneda identifies any family with the pullback of the universal subgroup. -/
theorem represented_subgroup_is_baseChange
    (n : ℕ) (M : Type u) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    {P T : Over S}
    (e : (TorsionQuotient.SubgroupFunctor.subgroupChoiceFunctor A n M).RepresentableBy P) (b : T ⟶ P) :
    e.homEquiv b = (e.homEquiv (𝟙 P)).baseChange b := by
  exact e.homEquiv_eq b

/-- The open support locus represents exactly the supported subgroup functor. -/
noncomputable def supportedSubgroups_representableBy_open
    (n : ℕ) (M : Type u) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (projectorLift : A ⟶ A)
    {P : Over S}
    (e : (TorsionQuotient.SubgroupFunctor.subgroupChoiceFunctor A n M).RepresentableBy P)
    (U : P.left.Opens)
    (hU : ∀ (T : Over S) (b : T ⟶ P),
      (∀ t : T.left, b.left t ∈ U) ↔
        SubgroupFunctor.Construction.SupportedOn ((e.homEquiv (𝟙 P)).subgroup.baseChange b) projectorLift) :
    (SubgroupFunctor.Construction.supportedSubgroupFunctor A n M projectorLift).RepresentableBy (openParameter P U) := by
  let C := openParameter P U
  let j : C ⟶ P := openParameterι P U
  have hj : Mono j := by
    have : Mono j.left := inferInstanceAs (Mono U.ι)
    exact Over.mono_of_mono_left j
  let toSupported {T : Over S} (x : T ⟶ C) : SubgroupFunctor.Construction.SupportedChoice A n M projectorLift T :=
    ⟨e.homEquiv (x ≫ j), by
      rw [represented_subgroup_is_baseChange]
      apply (hU T (x ≫ j)).mp
      intro t
      exact (x.left t).property⟩
  have hinj (T : Over S) : Function.Injective (@toSupported T) := by
    intro x y hxy
    apply (cancel_mono j).mp
    apply e.homEquiv.injective
    exact congrArg Subtype.val hxy
  have hsurj (T : Over S) : Function.Surjective (@toSupported T) := by
    intro F
    let b := e.homEquiv.symm F.val
    have hb : e.homEquiv b = F.val := e.homEquiv.apply_symm_apply F.val
    have hsupport : SubgroupFunctor.Construction.SupportedOn ((e.homEquiv (𝟙 P)).subgroup.baseChange b) projectorLift := by
      have he := represented_subgroup_is_baseChange n M e b
      rw [hb] at he
      have heS : F.val.subgroup = (e.homEquiv (𝟙 P)).subgroup.baseChange b :=
        congrArg (fun x : TorsionQuotient.SubgroupFunctor.SubgroupChoice A n M T => x.subgroup) he
      exact heS ▸ F.property
    have hrange : Set.range b.left ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι, Set.range_subset_iff]
      exact (hU T b).mpr hsupport
    let l := IsOpenImmersion.lift U.ι b.left hrange
    have hl : l ≫ U.ι = b.left := IsOpenImmersion.lift_fac _ _ hrange
    have hlbase : l ≫ C.hom = T.hom := by
      change l ≫ (U.ι ≫ P.hom) = T.hom
      rw [← Category.assoc, hl, b.w]
    let x : T ⟶ C := Over.homMk l hlbase
    have hx : x ≫ j = b := Over.OverMorphism.ext hl
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change e.homEquiv (x ≫ j) = F.val
    rw [hx, hb]
  refine {
    homEquiv := fun {T} => Equiv.ofBijective (@toSupported T) ⟨hinj T, hsurj T⟩
    homEquiv_comp := ?_
  }
  intro X X' f g
  apply Subtype.ext
  change e.homEquiv ((f ≫ g) ≫ j) =
    (e.homEquiv (g ≫ j)).baseChange f
  rw [Category.assoc]
  exact e.homEquiv_comp f (g ≫ j)

/-- TorsionQuotient implies finite etale representability for subgroups on each chosen
block, with the given elementary module type. No extra representability
or identification hypothesis is supplied for the block functor. -/
theorem finite_etale_supported_subgroups_of_TorsionQuotient
    (n : ℕ) (M : Type u) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (projectorLift : A ⟶ A) [IsMonHom projectorLift]
    (h_TorsionQuotient : IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom ∧
      Etale (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom ∧
      ∃ P : Over S,
        IsFinite P.hom ∧ Etale P.hom ∧
        Nonempty (uliftYoneda.{u + 1}.obj P ≅ TorsionQuotient.SubgroupFunctor.subgroupChoiceFunctor A n M)) :
    ∃ C : Over S,
      IsFinite C.hom ∧ Etale C.hom ∧
      Nonempty ((SubgroupFunctor.Construction.supportedSubgroupFunctor A n M projectorLift).RepresentableBy C) := by
  classical
  obtain ⟨htorsionfinite, htorsionetale, P, hfinite, hetale, ⟨eIso⟩⟩ := h_TorsionQuotient
  let e := (Functor.RepresentableBy.equivUliftYonedaIso
    (TorsionQuotient.SubgroupFunctor.subgroupChoiceFunctor A n M) P).symm eIso
  let F := e.homEquiv (𝟙 P)
  obtain ⟨R⟩ := F.geometric
  obtain ⟨U, hUfinite, hUetale, hU⟩ := SubgroupLocus.Construction.finite_etale_block_support_locus n M F R
    projectorLift ⟨htorsionfinite, htorsionetale⟩
  have : IsFinite U.ι := hUfinite
  have : Etale U.ι := hUetale
  have : IsFinite P.hom := hfinite
  have : Etale P.hom := hetale
  refine ⟨openParameter P U, ?_, ?_, ?_⟩
  · change IsFinite (U.ι ≫ P.hom)
    infer_instance
  · change Etale (U.ι ≫ P.hom)
    infer_instance
  · exact ⟨supportedSubgroups_representableBy_open n M projectorLift e U hU⟩

/-- The characteristic-zero version used for the universal family in IsogenyQuotient.
Its TorsionQuotient hypothesis is the complete repaired prerequisite proposition. -/
theorem characteristic_zero_block_subgroups
    {K : Type u} [Field K] [CharZero K]
    (s : S ⟶ Spec (CommRingCat.of K))
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (n : ℕ) (hn : 0 < n)
    (M : Type u) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (projectorLift : A ⟶ A) [IsMonHom projectorLift]
    (h_TorsionQuotient : Unit.Construction.TorsionQuotientInput.{u}) :
    ∃ C : Over S,
      IsFinite C.hom ∧ Etale C.hom ∧
      Nonempty (uliftYoneda.{u + 1}.obj C ≅ SubgroupFunctor.Construction.supportedSubgroupFunctor A n M projectorLift) := by
  obtain ⟨C, hfinite, hetale, ⟨e⟩⟩ := finite_etale_supported_subgroups_of_TorsionQuotient
    n M projectorLift
    (h_TorsionQuotient A n hn (Unit.Construction.positive_integer_unit_on_characteristic_zero_base s n hn) M)
  exact ⟨C, hfinite, hetale,
    ⟨Functor.RepresentableBy.equivUliftYonedaIso
      (SubgroupFunctor.Construction.supportedSubgroupFunctor A n M projectorLift) C e⟩⟩

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupRepresentable.Construction
