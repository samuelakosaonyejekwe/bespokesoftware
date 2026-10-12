// Model registry. Each pack exports an array of models (see kit.js for the contract).
import flowAssurance from './flow-assurance.js';
import aerospace from './aerospace-space-classical.js';
import marine from './marine-offshore-structural.js';
import thermal from './thermal-process-cfd.js';
import electromagnetic from './em-waves-materials.js';
import relativity from './relativity-quantum.js';
import logic from './logic-thought.js';

export const MODELS = [...flowAssurance, ...aerospace, ...marine, ...thermal, ...electromagnetic, ...relativity, ...logic];
const byId = new Map(MODELS.map(m => [m.id, m]));
export const modelById = id => (id ? byId.get(id) || null : null);
