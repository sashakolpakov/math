import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Flags
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Graph
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Interface
import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition

/-! # PEL -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PEL.Construction

noncomputable section

/-! The central Hecke correspondences have a single branch over each
source point. Their actual scheme endomorphisms are constructed here. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]

def singletonPELFlag (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (t : TateComparison.Local.IntegralType s) {k : Type} [Field k] [IsAlgClosed k]
    {b : Spec (.of k) ⟶ Spec (.of K)} (x : D.GeometricPoint b)
    (c : Over.mk b ⟶ (D.correspondence t).cover)
    (hc : c ≫ (D.correspondence t).source = x) : D.PELFlag b x [t] where
  point i := if i = 0 then x else c ≫ (D.correspondence t).target
  start := by simp
  branch j := by
    have hj : j = 0 := by
      apply Fin.ext
      change j.val = 0
      have h : j.val < 1 := j.isLt
      omega
    subst j
    exact c
  source j := by
    fin_cases j
    simpa using hc
  target j := by
    fin_cases j
    simp

/-- TateComparison's actual flag equivalence and uniqueness of the central linear
flag prove bijectivity of the source on geometric points. -/
theorem central_source_geometric_bijective
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hflags : D.HasPolarizedFlagRealizations hIsogenyQuotient)
    (t : TateComparison.Local.IntegralType s) (a : Fin s → ℤ)
    (ha : ∀ v i, t.val.exponent v i = a v)
    (k : Type) [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ Spec (.of K)) :
    Function.Bijective
      (fun c : Over.mk b ⟶ (D.correspondence t).cover => c ≫ (D.correspondence t).source) := by
  constructor
  · intro c d hcd
    let x := c ≫ (D.correspondence t).source
    let F := singletonPELFlag D t x c rfl
    let G := singletonPELFlag D t x d hcd.symm
    obtain ⟨e, B, L₀, _, _, hh⟩ := hflags k b x
    obtain ⟨eqv, _, _, _⟩ := hh [t]
    have hFG : F = G := eqv.injective
      ((Flags.Construction.central_singleton_flag_unique q L₀ t a ha (eqv F)).trans
        (Flags.Construction.central_singleton_flag_unique q L₀ t a ha (eqv G)).symm)
    exact congrArg (fun H => H.branch (0 : Fin 1)) hFG
  · intro x
    obtain ⟨e, B, L₀, _, _, hh⟩ := hflags k b x
    obtain ⟨eqv, _, _, _⟩ := hh [t]
    let F := eqv.symm (Flags.Construction.centralSingletonFlag q L₀ t a ha)
    refine ⟨F.branch (0 : Fin 1), ?_⟩
    exact (F.source (0 : Fin 1)).trans F.start

/-- The central source cover is isomorphic to the entire moduli scheme. -/
theorem central_correspondence_source_isIso
    (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgeometry : D.HasIntegralModelGeometry)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hflags : D.HasPolarizedFlagRealizations hIsogenyQuotient)
    (t : TateComparison.Local.IntegralType s) (a : Fin s → ℤ)
    (ha : ∀ v i, t.val.exponent v i = a v) :
    IsIso (D.correspondence t).source := by
  have : Smooth D.model.space.hom := hgeometry.smooth
  have : IsProper D.model.space.hom := hgeometry.proper
  have : Smooth D.space.hom := inferInstanceAs
    (Smooth (CategoryTheory.Limits.pullback.snd D.model.space.hom D.generic))
  have : IsProper D.space.hom := inferInstanceAs
    (IsProper (CategoryTheory.Limits.pullback.snd D.model.space.hom D.generic))
  have : IsReduced D.space.left := Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced D.space.hom
  have : IsLocallyNoetherian D.space.left :=
    LocallyOfFiniteType.isLocallyNoetherian D.space.hom
  exact Graph.Construction.finite_etale_isIso_of_geometric_bijective (D.correspondence t).source
    (central_source_geometric_bijective D hIsogenyQuotient hflags t a ha)

/-- This is the actual target morphism composed with the inverse source
of the central correspondence, rather than externally supplied action data. -/
def centralModuliMap (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgeometry : D.HasIntegralModelGeometry)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hflags : D.HasPolarizedFlagRealizations hIsogenyQuotient)
    (t : TateComparison.Local.IntegralType s) (a : Fin s → ℤ)
    (ha : ∀ v i, t.val.exponent v i = a v) : D.space ⟶ D.space := by
  have := central_correspondence_source_isIso D hgeometry hIsogenyQuotient hflags t a ha
  exact Interface.Construction.correspondenceMap (D.correspondence t)

theorem centralModuliMap_source (D : TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hgeometry : D.HasIntegralModelGeometry)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hflags : D.HasPolarizedFlagRealizations hIsogenyQuotient)
    (t : TateComparison.Local.IntegralType s) (a : Fin s → ℤ)
    (ha : ∀ v i, t.val.exponent v i = a v) :
    (D.correspondence t).source ≫ centralModuliMap D hgeometry hIsogenyQuotient hflags t a ha =
      (D.correspondence t).target := by
  have := central_correspondence_source_isIso D hgeometry hIsogenyQuotient hflags t a ha
  exact Interface.Construction.correspondenceMap_source _

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PEL.Construction
