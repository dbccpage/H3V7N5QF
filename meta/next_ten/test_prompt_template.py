"""Check future prompt text without regenerating any retained proposal package."""

from __future__ import annotations

import hashlib
import json
import unittest

import make_packages as packages


class PromptTemplateTests(unittest.TestCase):
    def render_selected(self) -> list[str]:
        items = json.loads((packages.HERE / 'candidates.json').read_text(encoding='utf-8'))
        by_id = {item['id']: item for item in items}
        selected = json.loads((packages.HERE / 'ranking.json').read_text(encoding='utf-8'))['top_ten']
        return [packages.make_prompt(by_id[ident], packages.DETAILS[ident], rank)
                for rank, ident in enumerate(selected, 1)]

    def test_future_prompts_name_the_actual_layout_without_the_dead_reference(self) -> None:
        prompts = self.render_selected()
        self.assertEqual(len(prompts), 10)
        for prompt in prompts:
            self.assertNotIn('docs/index/topics.md', prompt)
            for path in ('code/<ordinal>/', 'code/run_<ordinal>.py', 'tests/',
                         'lean4/<Ordinal>/', 'evidence/<ordinal>/', 'paper/<ordinal>/'):
                self.assertIn(path, prompt)
            self.assertIn('Do not modify `prompt/`.', prompt)

    def test_rendering_preserves_installed_inputs_and_retained_packages(self) -> None:
        paths = list((packages.ROOT / 'prompt').rglob('*')) + list(packages.HERE.glob('[0-9][0-9]-*/*'))
        files = [path for path in paths if path.is_file()]
        self.assertGreater(len(files), 50)
        before = {path: hashlib.sha256(path.read_bytes()).hexdigest() for path in files}
        self.render_selected()
        self.assertEqual(before, {path: hashlib.sha256(path.read_bytes()).hexdigest() for path in files})


if __name__ == '__main__':
    unittest.main()
