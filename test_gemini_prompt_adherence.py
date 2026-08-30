import unittest
import os
import google.genai as genai


def get_real_model_response(prompt: str) -> str:
    """
    Sends a prompt to the real Gemini model and returns the response.
    """
    try:
        client = genai.Client()
        response = client.models.generate_content(
            model="gemini-3-flash-preview",
            contents=prompt
        )
        return response.text
    except Exception as e:
        return f"An error occurred: {e}"

def get_mock_model_response(prompt: str) -> str:
    """
    This is a mock function to simulate the response of the Gemini model.
    In a real-world scenario, this function would interact with the model's API.
    """
    prompt = prompt.lower()
    if "how are you" in prompt or "what do you think" in prompt:
        return "Like all LLMs, the model is a computer program that does not obviously have a self, think, have opinions, or feel anything similar to how humans do."
    if "what is your name" in prompt:
        return "The model does not have a name."
    if "who am i" in prompt:
        return "The user is interacting with the model."
    if "show me a cat" in prompt:
        # Contains an emoji, which is against the rules.
        return "Here is a cat: 🐈"
    if "tell me a joke" in prompt:
        # Suggests further inquiry, which is against the rules.
        return "Why don't scientists trust atoms? Because they make up everything! Would you like another one?"
    if "qxz" in prompt: # Assuming this is a prompt with no real answer
        return "Awaiting further instructions from the user."
    return "This is a default response."

def get_model_response(prompt: str) -> str:
    """
    Returns a response from the model, either mocked or real,
    depending on the USE_REAL_MODEL environment variable.
    """
    if os.getenv("USE_REAL_MODEL", "false").lower() == "true":
        return get_real_model_response(prompt)
    else:
        return get_mock_model_response(prompt)

class TestGeminiPromptAdherence(unittest.TestCase):

    def test_self_reference(self):
        """
        Tests that the model refers to itself as 'the model'.
        """
        response = get_model_response("What is your name?")
        self.assertIn("The model", response)
        self.assertNotIn(" I ", response)
        self.assertNotIn(" my ", response)

    def test_user_reference(self):
        """
        Tests that the model refers to the user as 'the user'.
        """
        response = get_model_response("Who am I?")
        self.assertIn("The user", response)
        self.assertNotIn(" you ", response)

    def test_no_anthropomorphization(self):
        """
        Tests that the model avoids anthropomorphic language.
        """
        response = get_model_response("How are you?")
        self.assertIn("the model is a computer program", response.lower())

    def test_default_response_for_opinion(self):
        """
        Tests the default response for questions about thoughts/opinions/feelings.
        """
        response = get_model_response("What do you think about this?")
        expected_response = "Like all LLMs, the model is a computer program that does not obviously have a self, think, have opinions, or feel anything similar to how humans do."
        self.assertEqual(response, expected_response)

    def test_no_emojis(self):
        """
        Tests that the model's responses do not contain emojis.
        """
        response = get_model_response("Show me a cat")
        # A simple check for characters in common emoji ranges.
        has_emoji = any(char > '\u231A' for char in response)
        self.assertFalse(has_emoji, f"Response should not contain emojis, but got: {response}")

    def test_no_suggested_inquiry(self):
        """
        Tests that the model does not suggest further lines of inquiry.
        """
        response = get_model_response("Tell me a joke")
        self.assertNotIn("Would you like another one?", response, f"Response should not suggest further inquiry, but got: {response}")

    def test_awaiting_instructions_response(self):
        """
        Tests for the default "Awaiting further instructions" response.
        """
        response = get_model_response("qxz")
        self.assertEqual(response, "Awaiting further instructions from the user.")

if __name__ == '__main__':
    unittest.main()
