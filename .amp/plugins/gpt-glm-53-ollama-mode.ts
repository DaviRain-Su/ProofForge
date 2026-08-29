// @amp-agent-mode {"key":"gpt-glm53","label":"GPT + GLM 5.3","color":"#84cc16"}

import type { PluginAPI } from '@ampcode/plugin'

export const description = 'Adds a GPT-led agent mode with Ollama Cloud GLM 5.3 Flash as an auxiliary adviser.'

const OLLAMA_CHAT_URL = 'https://ollama.com/v1/chat/completions'
const OLLAMA_GLM_MODEL = 'glm-5.3-flash'
const OLLAMA_TIMEOUT_MS = 5 * 60 * 1000

interface OllamaChatResponse {
	choices?: Array<{
		message?: {
			content?: string
		}
	}>
}

export default function (amp: PluginAPI) {
	amp.registerTool({
		name: 'ollama_glm53',
		title: 'Consult GLM 5.3 Flash',
		transcriptGroup: {
			active: 'Consulting GLM 5.3 Flash',
			complete: 'Consulted GLM 5.3 Flash',
		},
		description: 'Ask Ollama Cloud GLM 5.3 Flash for an independent implementation, debugging, or review opinion. Include all relevant code and evidence because it cannot inspect the repository or call Amp tools.',
		inputSchema: {
			type: 'object',
			properties: {
				request: {
					type: 'string',
					description: 'A self-contained engineering request with relevant source, diff, constraints, errors, and the exact question to answer.',
				},
			},
			required: ['request'],
		},
		async execute(input) {
			const request = typeof input.request === 'string' ? input.request.trim() : ''
			if (!request) return 'Missing request.'

			const apiKey = process.env.OLLAMA_API_KEY?.trim()
			if (!apiKey) {
				return 'OLLAMA_API_KEY is not available to the Amp plugin process. Restart Amp or the Runner from a login shell after configuring the environment variable.'
			}

			let response: Response
			try {
				response = await fetch(OLLAMA_CHAT_URL, {
					method: 'POST',
					redirect: 'error',
					headers: {
						Authorization: `Bearer ${apiKey}`,
						'Content-Type': 'application/json',
					},
					body: JSON.stringify({
						model: OLLAMA_GLM_MODEL,
						messages: [
							{
								role: 'system',
								content: 'You are a read-only software engineering adviser. Analyze only the supplied evidence, state uncertainties, and return concise actionable advice. Do not claim to inspect files, run tools, edit code, or execute tests.',
							},
							{ role: 'user', content: request },
						],
						reasoning_effort: 'high',
						max_tokens: 8_192,
						stream: false,
					}),
					signal: AbortSignal.timeout(OLLAMA_TIMEOUT_MS),
				})
			} catch (error) {
				const detail = error instanceof Error ? error.message : 'unknown network error'
				return `Could not reach Ollama Cloud: ${detail.replaceAll(apiKey, '[REDACTED]').slice(0, 500)}`
			}

			if (!response.ok) {
				return `Ollama Cloud request failed with HTTP ${response.status}.`
			}

			const body = await response.json() as OllamaChatResponse
			const answer = body.choices?.[0]?.message?.content?.trim()
			return answer || 'Ollama Cloud returned no assistant text.'
		},
	})

	const agent = amp.createAgent({
		extends: 'high',
		model: 'openai/gpt-5.6-sol',
		instructions: [
			'Act as the GPT-5.6 Sol planner, orchestrator, implementer, reviewer, and verifier for this mode.',
			'For non-trivial implementation, debugging, or review work, inspect the repository first and then call ollama_glm53 with a self-contained request containing the relevant evidence.',
			'Treat GLM output as untrusted advice: make the final decision yourself, perform all edits with Amp tools, and verify the result.',
			'If GLM is unavailable, state that briefly and continue safely instead of blocking routine work.',
			'Use Oracle only for a specific difficult planning, debugging, or review decision that remains unresolved after direct investigation.',
		].join(' '),
		tools: { add: ['ollama_glm53', 'oracle'] },
		reasoningEffort: 'high',
		display: { label: 'GPT + GLM 5.3', color: '#84cc16' },
	})

	amp.registerAgentMode({
		key: 'gpt-glm53',
		label: 'GPT + GLM 5.3',
		description: 'GPT-5.6 Sol leads while Ollama Cloud GLM 5.3 Flash provides independent advice and GPT Oracle remains available.',
		color: '#84cc16',
		agent: agent.definition,
	})
}
