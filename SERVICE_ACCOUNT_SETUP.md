# Service Account Setup Instructions

## For Project Owner (You)

### Distributing the Service Account Key:

1. **Download the service account key** from Google Cloud Console:
   - Go to [Google Cloud Console](https://console.cloud.google.com/)
   - Navigate to: IAM & Admin → Service Accounts
   - Find: `service@altera-labs.iam.gserviceaccount.com`
   - Click Actions → Create Key → JSON
   - Download the JSON file

2. **Securely share with team members**:
   - Rename the file to `service-account-key.json`
   - Share via secure channel (encrypted email, secure file sharing, etc.)
   - **Never commit this file to git or share publicly**

3. **Instructions to give team members**:
   ```
   Save the attached service-account-key.json file in your Altera-Labs project root directory, 
   then follow the authentication steps in the README.md file.
   ```

## For Team Members

Follow the authentication instructions in the main [README.md](./README.md) file under the "Authenticate with Service Account" section.

## Security Notes

- The service account key provides access to Google Cloud resources
- Keep it secure and never share publicly
- If compromised, regenerate the key in Google Cloud Console
- The key is already excluded from git via `.gitignore`
