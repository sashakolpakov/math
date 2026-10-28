import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Scalar
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Etale

/-! # Scalar Isogeny -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ScalarIsogeny.Construction

noncomputable section

/-! The principal scalar's finite etale geometry is proved from the
ordinary abelian-scheme properties and its exact nonzero norm. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

/-- A finite etale group endomorphism is onto a group scheme with
geometrically connected fibers: its clopen image meets each fiber at zero. -/
theorem surjective_of_proper_etale_group_end
    {S : Scheme} (B : Over S) [GrpObj B] [IsCommMonObj B]
    [GeometricallyConnected B.hom]
    (f : B ⟶ B) [IsMonHom f] [IsProper f.left] [Etale f.left] : Surjective f.left := by
  constructor
  intro y
  let s := B.hom y
  let z := η[B].left s
  have hz : B.hom z = s := by
    have he := congrArg (fun h : S ⟶ S => h s) η[B].w
    exact he
  have hfz : f.left z = z := by
    have he := congrArg (fun h => h.left s) (IsMonHom.one_hom f)
    exact he
  have hcl : IsClopen (Set.range f.left) :=
    ⟨f.left.isClosedMap.isClosed_range, f.left.isOpenMap.isOpen_range⟩
  have hinter : ((B.hom ⁻¹' {s}) ∩ Set.range f.left).Nonempty :=
    ⟨z, hz, z, hfz⟩
  have hsub := (B.hom.isConnected_preimage_singleton s).isPreconnected.subset_isClopen hcl hinter
  exact hsub (show y ∈ B.hom ⁻¹' {s} from rfl)

/-- Multiplication by a base unit is a finite etale surjection on an
abelian scheme. Etaleness uses the checked infinitesimal TorsionQuotient proof. -/
theorem abelian_multiplier_finite_etale_surjective
    {S : Scheme} {g : ℕ} (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (n : ℕ) (hn : ∀ x : S, IsUnit (n : S.presheaf.stalk x)) :
    IsFinite ((𝟙 B.scheme) ^ n).left ∧ Etale ((𝟙 B.scheme) ^ n).left ∧
      Surjective ((𝟙 B.scheme) ^ n).left := by
  have : IsProper ((𝟙 B.scheme) ^ n).left := TorsionQuotient.Quasi.TorsionGeometry.power_isProper B.scheme n
  have : Etale ((𝟙 B.scheme) ^ n).left := TorsionQuotient.Etale.TorsionEtale.power_etale B.scheme n hn
  have : IsFinite ((𝟙 B.scheme) ^ n).left :=
    TorsionQuotient.Quasi.TorsionGeometry.finite_of_proper_formallyUnramified _
  have : IsMonHom ((𝟙 B.scheme) ^ n) := by
    rw [← Scalar.Construction.scalar_natCast_schemeMap]
    infer_instance
  exact ⟨inferInstance, inferInstance, surjective_of_proper_etale_group_end B.scheme _⟩

/-- Every nonzero integer is a unit on a scheme over a characteristic-zero field. -/
theorem nat_unit_on_charZero_scheme {K : Type} [Field K] [CharZero K]
    {S : Scheme} (p : S ⟶ Spec (.of K)) (n : ℕ) (hn : n ≠ 0) :
    ∀ x : S, IsUnit (n : S.presheaf.stalk x) := by
  intro x
  have hu : IsUnit (n : K) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)
  let r : K →+* S.presheaf.stalk x :=
    (S.presheaf.germ ⊤ x (by trivial)).hom.comp
      (p.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)
  simpa only [map_natCast] using hu.map r

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [CharZero K] {g N : ℕ} {S : Scheme}

/-- The scalar PEL isogeny is now constructed without any assumed
finiteness, flatness, surjectivity, or correspondence compatibility. -/
def scalarPELIsogeny_of_norm
    (B : TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N S)
    (base : S ⟶ Spec (.of K))
    (hRosati : B.IsRosatiCompatible
      (NumberField.IsCMField.ringOfIntegersComplexConj E).toRingHom)
    (b : NumberField.RingOfIntegers E) (n : ℕ) (hn : n ≠ 0)
    (hnorm : b * NumberField.IsCMField.ringOfIntegersComplexConj E b = n)
    (hlevel : Marking.Construction.levelReduction E N b = 1) : TateComparison.PELIsogenies.PELIsogeny B B n := by
  have hh := abelian_multiplier_finite_etale_surjective B.abelian n
    (nat_unit_on_charZero_scheme base n hn)
  have := hh.1
  have := hh.2.1
  have := hh.2.2
  exact Scalar.Construction.scalarPELIsogeny_of_finiteEtale_multiplier B hRosati b n hnorm hlevel

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ScalarIsogeny.Construction
