import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.BasisAffineChart

/-! # Rank One Projective -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.RankOneProjective.BundleCycles

noncomputable section

/-! The actual projective spectrum of a free module of rank one is
the coefficient spectrum via its native structure morphism. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R : Type) [CommRing R]

instance symmetricRankOneChart_isIso :
    IsIso (BasisAffineChart.BundleCycles.symmetricBasisAffineChartMap (Module.Basis.singleton Unit R) ()) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply top_unique
  intro x _
  obtain ⟨i, y, rfl⟩ := (BasisCover.BundleCycles.symmetricBasisCover (Module.Basis.singleton Unit R)).openCover.exists_eq x
  cases i
  have hr : Set.range ((BasisCover.BundleCycles.symmetricBasisCover (Module.Basis.singleton Unit R)).f ()) =
      Set.range (BasisAffineChart.BundleCycles.symmetricBasisAffineChartMap (Module.Basis.singleton Unit R) ()) :=
    congrArg (fun U : (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R R).Opens => (U : Set (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R R)))
      ((BasisCover.BundleCycles.symmetricBasisCover_opensRange (Module.Basis.singleton Unit R) ()).trans
        (BasisAffineChart.BundleCycles.symmetricBasisAffineChartMap_opensRange (Module.Basis.singleton Unit R) ()).symm)
  change ((BasisCover.BundleCycles.symmetricBasisCover (Module.Basis.singleton Unit R)).f ()) y ∈
    Set.range (BasisAffineChart.BundleCycles.symmetricBasisAffineChartMap (Module.Basis.singleton Unit R) ())
  exact hr ▸ Set.mem_range_self y

instance symmetricRankOneProjectiveToBase_isIso : IsIso (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R R) := by
  let j := BasisAffineChart.BundleCycles.symmetricBasisAffineChartMap (Module.Basis.singleton Unit R) ()
  let p := (AffineSpace {j : Unit // j ≠ ()} (Spec (.of R)) ↘ Spec (.of R))
  let : IsIso j := symmetricRankOneChart_isIso R
  let : IsEmpty {j : Unit // j ≠ ()} := ⟨fun j => j.property (Subsingleton.elim _ _)⟩
  let : IsIso p := inferInstanceAs (IsIso (AffineSpace {j : Unit // j ≠ ()} (Spec (.of R)) ↘ Spec (.of R)))
  have hjp : j ≫ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R R = p :=
    BasisAffineChart.BundleCycles.symmetricBasisAffineChartMap_over (Module.Basis.singleton Unit R) ()
  have hp : SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R R = inv j ≫ p := by
    exact (IsIso.inv_hom_id_assoc j (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R R)).symm.trans
      (congrArg (fun q => inv j ≫ q) hjp)
  rw [hp]
  infer_instance

def symmetricRankOneProjectiveIso : SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R R ≅ Spec (.of R) :=
  asIso (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R R)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.RankOneProjective.BundleCycles
