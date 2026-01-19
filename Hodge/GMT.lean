import Hodge.GMT.Current
import Hodge.GMT.IntegrationCurrent
import Hodge.GMT.CurrentToForm
import Hodge.GMT.PoincareDuality
import Hodge.GMT.FlatNormTopology
import Hodge.GMT.IntegralCurrentSpace
import Hodge.GMT.CalibratedGeometry
import Hodge.GMT.HarveyLawsonTheorem
import Hodge.GMT.FedererFleming

/-!
# `Hodge.GMT` (Compatibility Umbrella)

This module provides the file/module layout referenced by
`docs/OPERATIONAL_PLAN_5_AGENTS.md` for **Agent 5**.

The repository already contains most GMT infrastructure under `Hodge.Analytic.*`
(currents, integral currents, flat norm, etc.). The files under `Hodge/GMT/*` are
therefore thin wrappers/re-exports, so we avoid duplicating definitions while still
matching the planned module structure.
-/
