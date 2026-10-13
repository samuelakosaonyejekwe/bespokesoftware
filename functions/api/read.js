// Reads a prompt with a hosted language model and returns a structured interpretation. The model only proposes: the
// application checks every identifier, unit, number and equation it returns before using any of it.
import { SYSTEM } from '../../js/engine/reading-prompt.js';

const MODEL = '@cf/meta/llama-3.3-70b-instruct-fp8-fast';
// daily allowance: for everyone together, and for one address. Counted in a key-value store; only counts are kept.
const DAY_TOTAL = 150, DAY_EACH = 20;
const ALLOW = [/^https:\/\/samuelakosaonyejekwe\.github\.io$/, /^https:\/\/([a-z0-9-]+\.)?bespokesoftware\.pages\.dev$/, /^http:\/\/localhost(:\d+)?$/, /^http:\/\/127\.0\.0\.1(:\d+)?$/];
const cors = req => { const o = req.headers.get('Origin') || ''; return { 'Access-Control-Allow-Origin': ALLOW.some(r => r.test(o)) ? o : 'https://bespokesoftware.pages.dev', 'Access-Control-Allow-Methods': 'POST, OPTIONS', 'Access-Control-Allow-Headers': 'Content-Type', 'Access-Control-Max-Age': '86400', Vary: 'Origin' }; };
const json = (req, body, status = 200) => new Response(JSON.stringify(body), { status, headers: { 'Content-Type': 'application/json', 'Cache-Control': 'no-store', ...cors(req) } });

export async function onRequestOptions({ request }) { return new Response(null, { status: 204, headers: cors(request) }); }
export async function onRequestPost({ request, env }) {
  let body; try { body = await request.json(); } catch { return json(request, { error: 'Bad request' }, 400); }
  const prompt = String(body.prompt || '').slice(0, 6000), cat = Array.isArray(body.candidates) ? body.candidates.slice(0, 24) : [];
  if (prompt.trim().length < 3) return json(request, { error: 'Empty prompt' }, 400);
  const catalogue = JSON.stringify(cat).slice(0, 40000), feedback = String(body.feedback || '').slice(0, 700);
  if (!env.AI) return json(request, { error: 'No language model is attached to this host' }, 503);
  // requests are accepted only from the application's own pages
  const origin = request.headers.get('Origin') || '';
  if (!ALLOW.some(r => r.test(origin))) return json(request, { error: 'Not available from this page' }, 403);
  if (env.LIMITS) {
    const day = new Date().toISOString().slice(0, 10), ip = request.headers.get('CF-Connecting-IP') || 'unknown';
    const who = `${day}:ip:${[...new Uint8Array(await crypto.subtle.digest('SHA-256', new TextEncoder().encode(`${day}|${ip}`)))].slice(0, 8).map(b => b.toString(16).padStart(2, '0')).join('')}`;
    const [all, mine] = (await Promise.all([env.LIMITS.get(`${day}:all`), env.LIMITS.get(who)])).map(v => parseInt(v || '0', 10));
    if (all >= DAY_TOTAL) return json(request, { error: 'today’s shared allowance for language-model readings is used up' }, 429);
    if (mine >= DAY_EACH) return json(request, { error: 'today’s allowance for this connection is used up' }, 429);
    await Promise.all([env.LIMITS.put(`${day}:all`, String(all + 1), { expirationTtl: 172800 }), env.LIMITS.put(who, String(mine + 1), { expirationTtl: 172800 })]);
  }
  try {
    const out = await env.AI.run(MODEL, { messages: [{ role: 'system', content: SYSTEM }, { role: 'user', content: `CATALOGUE:\n${catalogue}\n\nQUESTION:\n${prompt}${feedback ? `\n\nYour previous answer was rejected for these reasons; correct them:\n${feedback}` : ''}` }], max_tokens: 1400, temperature: 0.1, response_format: { type: 'json_object' } });
    const text = typeof out.response === 'string' ? out.response : JSON.stringify(out.response ?? out);
    return json(request, { text, model: MODEL });
  } catch (err) { return json(request, { error: String(err && err.message || err).slice(0, 300) }, 502); }
}
