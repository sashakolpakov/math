import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GraphPowerIsoDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.ParameterFunctoriality

/-! # Graph Power Open Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GraphPowerOpenCover

noncomputable section

/-! Concrete open-cover form of normalized graph-power isomorphism
descent, and comparison of single-parameter with native pullbacks. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem bundleIso_of_singleParameterPullback
    {S : Scheme.{u}} (X : Over S) {U T : Over S} (c : U ⟶ T)
    (L M : Line.Bundles.LineBundle ((Over.pullback T.hom).obj X).left)
    (h : Nonempty ((L.pullback (Single.ParameterBaseChange.singleParameterBaseChangeMap c X)).sheaf ≅
      (M.pullback (Single.ParameterBaseChange.singleParameterBaseChangeMap c X)).sheaf)) :
    Nonempty ((L.pullback (pullback.fst ((Over.pullback T.hom).obj X).hom c.left)).sheaf ≅
      (M.pullback (pullback.fst ((Over.pullback T.hom).obj X).hom c.left)).sheaf) := by
  apply Quotient.exact (s := Line.Bundles.LineBundle.isoSetoid _)
    (a := L.pullback (pullback.fst ((Over.pullback T.hom).obj X).hom c.left))
    (b := M.pullback (pullback.fst ((Over.pullback T.hom).obj X).hom c.left))
  apply (Line.Bundles.LineBundle.pullbackIso ((Over.forget U.left).mapIso
    (Single.ParameterBaseChange.singleParameterBaseChangeIso c X))).injective
  change Line.Bundles.LineBundle.pullbackClass (Single.ParameterBaseChange.singleParameterBaseChangeIso c X).hom.left
      (Line.Bundles.LineBundle.pullbackClass (pullback.fst ((Over.pullback T.hom).obj X).hom c.left)
        (Line.Bundles.LineBundle.classOf L)) =
    Line.Bundles.LineBundle.pullbackClass (Single.ParameterBaseChange.singleParameterBaseChangeIso c X).hom.left
      (Line.Bundles.LineBundle.pullbackClass (pullback.fst ((Over.pullback T.hom).obj X).hom c.left)
        (Line.Bundles.LineBundle.classOf M))
  have he : Line.Bundles.LineBundle.pullbackClass (Single.ParameterBaseChange.singleParameterBaseChangeMap c X) (Line.Bundles.LineBundle.classOf L) =
      Line.Bundles.LineBundle.pullbackClass (Single.ParameterBaseChange.singleParameterBaseChangeMap c X) (Line.Bundles.LineBundle.classOf M) := Quotient.sound h
  simpa only [← Line.Bundles.LineBundle.pullbackClass_comp, Single.ParameterFunctoriality.singleParameterBaseChangeIso_hom_fst] using he

theorem zeroNormalizedGraphPowerIso_of_openCover
    {S T : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (t : T ⟶ S)
    (level : (A.pullback t).FullLevel N) (D : Dual.Data.DualAbelianData (A.pullback t))
    (pol : PolarizationData.Polarization D δ) (L : Line.Bundles.LineBundle A.scheme.left) (d : ℕ) (C : T.OpenCover.{u})
    (hlocal : ∀ i, Nonempty
      ((((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom t)).pullback
        (pullback.fst (A.pullback t).scheme.hom (C.f i))).sheaf ≅
      (((PoincareGraph.Bundles.poincareGraphBundle D pol.isogeny.hom).tensorPower d).pullback
        (pullback.fst (A.pullback t).scheme.hom (C.f i))).sheaf)) :
    Nonempty (((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom t)).sheaf ≅
      ((PoincareGraph.Bundles.poincareGraphBundle D pol.isogeny.hom).tensorPower d).sheaf) := by
  let X := (A.pullback t).scheme
  let M := (A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom t)
  let G := (PoincareGraph.Bundles.poincareGraphBundle D pol.isogeny.hom).tensorPower d
  let F := Relative.BundleIsoSheaf.relativeBundleIsoPresheaf X.hom M G
  let V : C.I₀ → Over T := fun i => Over.mk (C.f i)
  let j : ∀ i, V i ⟶ Over.mk (𝟙 T) := fun i => Over.homMk (C.f i) (Category.comp_id _)
  let R := Sieve.ofArrows V j
  have hR : R ∈ (Scheme.zariskiTopology.over T) (Over.mk (𝟙 T)) := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact C.mem_grothendieckTopology
  have hi (i : C.I₀) : Nonempty (F.obj (.op (V i))) := by
    change Nonempty ((M.pullback (pullback.snd (C.f i) X.hom)).sheaf ≅
      (G.pullback (pullback.snd (C.f i) X.hom)).sheaf)
    have hc : Line.Bundles.LineBundle.pullbackClass (pullback.fst X.hom (C.f i)) (Line.Bundles.LineBundle.classOf M) =
        Line.Bundles.LineBundle.pullbackClass (pullback.fst X.hom (C.f i)) (Line.Bundles.LineBundle.classOf G) :=
      Quotient.sound (hlocal i)
    have h := congrArg (Line.Bundles.LineBundle.pullbackClass (pullbackSymmetry X.hom (C.f i)).inv) hc
    apply Quotient.exact (s := Line.Bundles.LineBundle.isoSetoid _)
      (a := M.pullback (pullback.snd (C.f i) X.hom))
      (b := G.pullback (pullback.snd (C.f i) X.hom))
    change Line.Bundles.LineBundle.pullbackClass (pullback.snd (C.f i) X.hom) (Line.Bundles.LineBundle.classOf M) =
      Line.Bundles.LineBundle.pullbackClass (pullback.snd (C.f i) X.hom) (Line.Bundles.LineBundle.classOf G)
    simpa only [← Line.Bundles.LineBundle.pullbackClass_comp, pullbackSymmetry_inv_comp_fst] using h
  apply GraphPowerIsoDescent.zeroNormalizedGraphPowerIso_of_cover A P t level D pol L d R hR
  intro U f hf
  obtain ⟨i, a, _⟩ := (Sieve.mem_ofArrows_iff V j f).mp hf
  exact (hi i).map (F.map a.op)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GraphPowerOpenCover
